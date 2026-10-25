/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseEnvironment
import Vegas.Game.SequentialPhaseHandle
import Vegas.Game.RecoveryDecodedDebt
import Vegas.Game.PhaseTerminalFailure

/-! # Source debt persists through actual singleton phase continuations

Only the physical current state is used. Accepted packets retain the active
attempt, rejected packets stutter, and every actual environment kernel projects
to the original recovery kernel. Source step-closed properties consequently
survive arbitrary continuations, including after a foreign public exclusion.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (plan : RuntimePhasePlan (graph setup))
  (singletons : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
  (inputs : PMF (graph setup).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  {source : BehavioralProfile setup.program} {property : ProtocolState setup.program → Prop}

local notation "app" => phaseApplication (runtime setup) leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

include singletons

private theorem handle_decoded_current {control : (app).Control}
    (trace : ((app).protocol (initial) horizon scheduler).Trace (some control))
    (closed : StepClosed setup property)
    (valid : RecoveryDecoded source property control.execution.application.current)
    (message : Message Player (CommitAttemptPacket (graph setup)))
    (next : PhaseRuntimeState (graph setup))
    (accepted : control.execution.application.handle (runtime setup) message = some next) :
    RecoveryDecoded source property next.current := by
  have activeAttempt : message.payload.attempt = control.execution.application.attempt := by
    by_contra retired
    rw [PhaseRuntimeState.handle_retired (runtime setup) _ message retired] at accepted
    cases accepted
  have live := (phaseApplication_live (runtime setup) leaks).history (initial) horizon scheduler
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact ⟨PhaseRuntimeState.initial_frontier plan draw,
        PhaseRuntimeState.initial_live plan draw⟩)
    trace
  have suffix := phasePlanSuffix_history (runtime setup) leaks plan inputs horizon scheduler trace
  have projected := PhaseRuntimeState.handle_current_sequential (runtime setup)
    control.execution.application live.1 live.2
    (phaseStoredCheckpoint_history (runtime setup) leaks plan inputs horizon scheduler trace)
    (phaseHistoryCheckpoint_history (runtime setup) leaks plan inputs horizon scheduler trace)
    (phaseAcceptedCheckpointFrame_history (runtime setup) leaks plan inputs horizon scheduler trace)
    (phaseExclusionRecord_history (runtime setup) leaks plan inputs horizon scheduler trace)
    (fun phase member => singletons phase (suffix.subset member)) message
    (fun _native _accepted => activeAttempt)
  rw [accepted, Option.map_some] at projected
  exact valid.handle closed (runtime setup) ⟨message.id, message.payload.packet⟩ next.current
    projected.symm

private theorem environmentStep_decoded_current {control : (app).Control}
    (trace : ((app).protocol (initial) horizon scheduler).Trace (some control))
    (closed : StepClosed setup property)
    (valid : RecoveryDecoded source property control.execution.application.current)
    (operation : (app).Command) (next : (app).Execution)
    (supported : next ∈ (control.execution.environmentStep (app) operation).support) :
    RecoveryDecoded source property next.application.current := by
  apply (app).environmentStep_cases control.execution next operation supported
    (predicate := fun _ next => RecoveryDecoded source property next.application.current)
  · exact valid
  · exact fun _ _ _ => valid
  · intro identity
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases found : control.execution.network.lookup identity with
    | none => exact valid
    | some message =>
        change RecoveryDecoded source property
          (((app).handle control.execution.application message).getD
            control.execution.application).current
        cases accepted : (app).handle control.execution.application message with
        | none => exact valid
        | some after =>
            exact handle_decoded_current setup leaks plan singletons inputs horizon scheduler trace
              closed valid message after accepted
  · intro command state supported
    have law := phase_environment_current_sequential_history (runtime setup) leaks plan singletons
      inputs horizon scheduler trace command
    have projected : state.current ∈
        ((control.execution.application.environment (runtime setup) command).map
          PhaseRuntimeState.current).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨state, supported, rfl⟩
    rw [law] at projected
    exact valid.environment closed (runtime setup) command state.current projected

/-- Actual initialized raw transitions preserve the original source property on
the complete current state, with no clear-region premise. -/
theorem phase_current_decoded_transition
    (closed : StepClosed setup property) (before after : (app).ProtocolState)
    (trace : ((app).protocol (initial) horizon scheduler).Trace before)
    (joint : Player → Option (app).Action)
    (valid : before.elim False fun control =>
      RecoveryDecoded source property control.execution.application.current)
    (reached : after ∈ ((app).transition (initial) horizon scheduler before joint).support) :
    after.elim False fun control =>
      RecoveryDecoded source property control.execution.application.current := by
  cases before with
  | none => exact valid.elim
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          cases chosen : (joint who).getD ⟨none⟩ with
          | mk transmission =>
              cases transmission with
              | none => exact valid
              | some material => exact valid.submit closed who material
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _chosen, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              exact environmentStep_decoded_current setup leaks plan singletons inputs horizon
                scheduler trace closed valid command next supported

section Continuation

variable [Fintype Player]

/-- Every terminal whole-policy continuation of an actual singleton phase
history with focal source debt pays the existing physical exclusion payoff.
The completion premise includes exhausted terminal controls. -/
theorem phase_owesFailure_terminal_payoff {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (menu : (app).ResponseMenu)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initial) horizon scheduler)
    (certificate : (menu.protocol (initial) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initial) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initial) horizon scheduler).History)
    (owed : history.state.elim False fun control => RecoveryDecoded source
      (ProtocolState.OwesFailure who setup.program) control.execution.application.current)
    (final : (menu.protocol (initial) horizon scheduler).History)
    (supported : final ∈ ((menu.information (initial) horizon scheduler).runBehavioralTerminalFrom
      certificate players history).support) :
    phaseExclusionBase setup .sequential (runtime setup) leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
      final.state who = excludedPayoff who := by
  let model := menu.information (initial) horizon scheduler
  let preserved := fun state : (app).ProtocolState =>
    Nonempty ((menu.protocol (initial) horizon scheduler).Trace state) ∧
      state.elim False fun control => RecoveryDecoded source
        (ProtocolState.OwesFailure who setup.program) control.execution.application.current
  have remains := model.runBehavioralTerminalFrom_support_closed
    certificate players preserved (by
      rintro before joint legal after ⟨⟨prior⟩, valid⟩ reached
      refine ⟨⟨.extend prior joint legal reached⟩, ?_⟩
      exact phase_current_decoded_transition setup leaks plan singletons inputs horizon scheduler
        (owesFailure_stepClosed who) before after
        (menu.toRawTrace (initial) horizon scheduler prior) joint valid reached)
    history ⟨⟨history.trace⟩, owed⟩ final supported
  have stopped := model.runBehavioralTerminalFrom_support_terminal
    certificate players history final supported
  cases current : final.state with
  | none => rw [current] at remains; exact remains.2.elim
  | some control =>
      rw [current] at remains stopped
      have trace := current ▸ menu.toRawTrace (initial) horizon scheduler final.trace
      let recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)) :=
        fun _ _ => PMF.pure ∅
      rw [phaseExclusionBase_eq_recoveryExclusionBase setup leaks recoveryLeaks
        parameter utility excludedPayoff control
          (phaseFailureCoverage_history (runtime setup) leaks plan inputs horizon scheduler trace)]
      exact recovery_owesFailure_exclusionBase_of_complete parameter utility excludedPayoff _ who
        remains.2 (completes control trace stopped)

/-- The expected payoff is fixed for arbitrary whole continuation policies,
including policies that use the additional archived phase observations. -/
theorem phase_owesFailure_expected_payoff {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (menu : (app).ResponseMenu)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initial) horizon scheduler)
    (certificate : (menu.protocol (initial) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initial) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initial) horizon scheduler).History)
    (owed : history.state.elim False fun control => RecoveryDecoded source
      (ProtocolState.OwesFailure who setup.program) control.execution.application.current) :
    expect ((menu.information (initial) horizon scheduler).runBehavioralTerminalFrom certificate
      players history) (fun final => phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          final.state who) = excludedPayoff who := by
  rw [expect_congr_on_support (g := fun _ => excludedPayoff who)
    (phase_owesFailure_terminal_payoff setup leaks plan singletons inputs horizon scheduler
      parameter utility excludedPayoff menu completes certificate players who history owed)]
  exact expect_constant _ _

end Continuation
end Vegas
