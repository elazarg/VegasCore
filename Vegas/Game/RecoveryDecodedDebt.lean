/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySourceFailure
import Vegas.Game.NativeExitContinuation
import Vegas.Pending.ExclusionService
import Vegas.Game.OnePacketIntendedProjection
import Vegas.Game.RevealServicePayoffs

/-! # Source debts persist through concrete recovery continuations

Automatic service follows actual graph steps. Its ordinary source decoding
preserves step-closed debts; no equality with source histories that omit automatic
choices is asserted. Full graph completion is needed only for a debt that has not
yet produced permanent runtime exclusion.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {profile : BehavioralProfile setup.program}
  {property : ProtocolState setup.program → Prop}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A step-closed source property holds at the actual compiled prefix of a
recovery state, together with an actual source residual at that prefix. -/
def RecoveryDecoded (profile : BehavioralProfile setup.program)
    (property : ProtocolState setup.program → Prop) (state : RecoveryState (graph setup)) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank state.native.config) ∧
    DecodedHolds property rank state.native.config

namespace RecoveryDecoded

variable {state : RecoveryState (graph setup)}

/-- The decoder of a legitimately reached native configuration supplies the
initial property for continuation arguments, including latent binding debt. -/
theorem of_decodedPoint (source : SourceFailureRecord profile state.native.config)
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup state.native.config = some point) (holds : property point) :
    RecoveryDecoded profile property state := by
  obtain ⟨rank, ⟨residual⟩, _⟩ := source
  rw [decodedPoint_eq residual] at decoded
  have same := Option.some.inj decoded
  refine ⟨rank, ⟨residual⟩, fun target read => ?_⟩
  rw [residual.decode, Option.some.injEq] at read
  subst target
  exact same.symm ▸ holds

/-- Every actual graph step preserves a source property closed under source steps. -/
theorem configStep (closed : StepClosed setup property)
    (valid : RecoveryDecoded profile property state) (next : RecoveryState (graph setup))
    (step : ConfigStep setup state.native.config next.native.config) :
    RecoveryDecoded profile property next := by
  obtain ⟨rank, ⟨residual⟩, holds⟩ := valid
  rcases step.prefix rank residual.checkpoint.ordered with same | advanced
  · have ordered : next.native.config.cut.IsPrefix rank := by
      rw [same]
      exact residual.checkpoint.ordered
    exact ⟨rank, residual.configStep step rank ordered,
      residual.decodedHolds_configStep closed holds step ordered⟩
  · exact ⟨rank + 1, residual.configStep step (rank + 1) advanced,
      residual.decodedHolds_configStep closed holds step advanced⟩

theorem drainFuel (closed : StepClosed setup property) (fuel : Nat)
    (valid : RecoveryDecoded profile property state) :
    RecoveryDecoded profile property (RecoveryState.drainFuel fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      unfold RecoveryState.drainFuel
      split
      · rename_i pending
        obtain ⟨action, member⟩ := state.completeAutomatic_step (Classical.choose pending)
          (Classical.choose_spec pending)
        exact ih (valid.configStep closed _ (Or.inr ⟨_, _, action, member⟩))
      · exact valid

theorem drain (closed : StepClosed setup property)
    (valid : RecoveryDecoded profile property state) :
    RecoveryDecoded profile property state.drain := valid.drainFuel closed _

theorem submit (closed : StepClosed setup property)
    (valid : RecoveryDecoded profile property state) (who : Player)
    (submission : WitnessedSubmission (graph setup)) :
    RecoveryDecoded profile property (state.submit who submission) := by
  apply valid.configStep closed _ (Or.inl ?_)
  change (submitStep _ who _).config = _
  rw [submitStep_config, (submission.call.register_facts who state.native).1]

theorem handle (closed : StepClosed setup property)
    (valid : RecoveryDecoded profile property state)
    (runtime : EventGraphRuntime (graph setup))
    (message : Message Player (WitnessedPacket (graph setup))) (next : RecoveryState (graph setup))
    (accepted : state.handle runtime message = some next) :
    RecoveryDecoded profile property next := by
  unfold RecoveryState.handle at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
      obtain ⟨event, _, ready, action, member⟩ :=
        handle_config_mem_step runtime state.native native _ rawAccepted
      exact (valid.configStep closed _ (Or.inr ⟨event, ready, action, member⟩)).drain closed
    · cases accepted

theorem environment (closed : StepClosed setup property)
    (valid : RecoveryDecoded profile property state)
    (runtime : EventGraphRuntime (graph setup)) (command : EnvironmentCommand (graph setup))
    (next : RecoveryState (graph setup))
    (reached : next ∈ (state.environment runtime command).support) :
    RecoveryDecoded profile property next := by
  rw [RecoveryState.environment, PMF.support_map] at reached
  obtain ⟨native, realized, rfl⟩ := reached
  have step : ConfigStep setup state.native.config native.config := by
    rcases completionStep_environmentStep runtime state.native native command realized with
      ⟨same, _, _⟩ | ⟨event, ready, action, member, _, _⟩
    · exact Or.inl same
    · exact Or.inr ⟨event, ready, action, member⟩
  exact (valid.configStep closed _ step).drain closed

end RecoveryDecoded

/-- A decoded source property at an initialized recovery protocol state. -/
def RecoveryDecodedState (profile : BehavioralProfile setup.program)
    (property : ProtocolState setup.program → Prop) :
    (recoveryApplication runtime leaks).ProtocolState → Prop
  | none => False
  | some control => RecoveryDecoded profile property control.execution.application

/-- Actual recovery transitions preserve every source step-closed decoded property. -/
theorem recoveryDecoded_transition (closed : StepClosed setup property)
    (initial : PMF (RecoveryState (graph setup))) (horizon : Nat)
    (scheduler : (recoveryApplication runtime leaks).Scheduler)
    (before after : (recoveryApplication runtime leaks).ProtocolState)
    (joint : Player → Option (recoveryApplication runtime leaks).Action)
    (valid : RecoveryDecodedState (runtime := runtime) (leaks := leaks) profile property before)
    (reached : after ∈ ((recoveryApplication runtime leaks).transition initial horizon
      scheduler before joint).support) :
    RecoveryDecodedState (runtime := runtime) (leaks := leaks) profile property after := by
  let app := recoveryApplication runtime leaks
  have invariant : app.Invariant (RecoveryDecoded profile property) :=
    ⟨fun _ who material valid => valid.submit closed who material,
      fun _ message next valid accepted => valid.handle closed _ message next accepted,
      fun _ command next valid realized => valid.environment closed _ command next realized⟩
  cases before with
  | none => exact valid.elim
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact invariant.respond execution who _ valid
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
              rw [← same]
              exact invariant.environmentStep execution next command valid supported

/-- A latent source debt fixes the recovery utility once the native graph is
complete, whether or not permanent runtime exclusion has already occurred. -/
theorem recovery_owesFailure_exclusionBase_of_complete {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (control : (recoveryApplication runtime leaks).Control) (who : Player)
    (owed : RecoveryDecoded profile (ProtocolState.OwesFailure who setup.program)
      control.execution.application)
    (complete : control.execution.application.native.config.cut.Terminal) :
    recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff (some control) who =
      excludedPayoff who := by
  by_cases excluded : who ∈ control.execution.application.excluded
  · exact recoveryExclusionBase_of_excluded (runtime := runtime) parameter utility excludedPayoff
      control who excluded
  · rw [recoveryExclusionBase_of_not_excluded (runtime := runtime) parameter utility
      excludedPayoff control who excluded]
    obtain ⟨rank, ⟨residual⟩, holds⟩ := owed
    have full := isPrefix_eventCount_of_terminal residual.checkpoint.ordered complete
    subst rank
    have read := sourceServicePrefix?_terminal_readout setup
      control.execution.application.native.config
    have decoded := residual.decode
    change sourceServicePrefix? setup (eventCount setup.program)
      control.execution.application.native.config = some _ at decoded
    have pointOwed := holds _ decoded
    rw [decoded] at read
    obtain ⟨terminal, terminalRead⟩ := ProtocolState.exists_readout_of_terminal setup.program _
      (decodeSourcePrefix?_terminal setup.program _ _ _ _ _ _ _ decoded)
    have failed := ProtocolState.failedReveals_pos_of_owesFailure who setup.program _ pointOwed
      terminalRead
    rw [exclusionBase_eq_readout, sourceReadout, serviceSourceReadout_eq_decode]
    change exclusionReadoutUtility setup parameter utility excludedPayoff
      (decodeState? (terminalRefs setup.program)
        control.execution.application.native.config.store) who = excludedPayoff who
    have terminalDecode : decodeState? (terminalRefs setup.program)
        control.execution.application.native.config.store = some terminal :=
      read.symm.trans terminalRead
    rw [terminalDecode]
    exact exclusionTerminalUtility_of_failed setup parameter utility excludedPayoff failed

section Continuation

variable [Fintype Player]

/-- Under actual recovery completion, every terminal continuation pays a player
already owing a source failure its fixed exclusion utility. -/
theorem recovery_owesFailure_exclusionBase {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (recoveryApplication runtime leaks).ResponseMenu)
    (initial : PMF (RecoveryState (graph setup))) (horizon : Nat)
    (scheduler : (recoveryApplication runtime leaks).Scheduler)
    (completes : Recovery.CompletesPlay runtime leaks initial horizon scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol initial horizon scheduler).History)
    (owed : RecoveryDecodedState (runtime := runtime) (leaks := leaks) profile
      (ProtocolState.OwesFailure who setup.program) history.state) :
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
      players history).support,
      recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff final.state who
        = excludedPayoff who :=
    by
  intro final supported
  have remains := (menu.information initial horizon
    scheduler).runBehavioralTerminalFrom_support_closed certificate players
      (RecoveryDecodedState (runtime := runtime) (leaks := leaks) profile
        (ProtocolState.OwesFailure who setup.program))
      (fun before joint _ after valid reached =>
        recoveryDecoded_transition (runtime := runtime) (owesFailure_stepClosed who) initial
          horizon scheduler
          before after joint valid reached) history owed final supported
  have stopped := (menu.information initial horizon
    scheduler).runBehavioralTerminalFrom_support_terminal certificate players history final
      supported
  cases state : final.state with
  | none => rw [state] at remains; exact remains.elim
  | some control =>
      rw [state] at remains stopped
      have trace := state ▸ menu.toRawTrace initial horizon scheduler final.trace
      exact recovery_owesFailure_exclusionBase_of_complete (runtime := runtime) parameter utility
        excludedPayoff control
        who remains (completes control trace stopped)


/-- The whole completed continuation law has the fixed utility of its source debt. -/
theorem recovery_owesFailure_expect_exclusionBase {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (recoveryApplication runtime leaks).ResponseMenu)
    (initial : PMF (RecoveryState (graph setup))) (horizon : Nat)
    (scheduler : (recoveryApplication runtime leaks).Scheduler)
    (completes : Recovery.CompletesPlay runtime leaks initial horizon scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol initial horizon scheduler).History)
    (owed : RecoveryDecodedState (runtime := runtime) (leaks := leaks) profile
      (ProtocolState.OwesFailure who setup.program) history.state) :
    expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
      players history) (fun final => recoveryExclusionBase (runtime := runtime) parameter utility
        excludedPayoff
        final.state who) = excludedPayoff who := by
  rw [expect_congr_on_support (g := fun _ => excludedPayoff who)
    (recovery_owesFailure_exclusionBase (runtime := runtime) parameter utility excludedPayoff menu
      initial horizon
      scheduler completes certificate players who history owed)]
  exact expect_constant _ _

end Continuation
end Vegas
