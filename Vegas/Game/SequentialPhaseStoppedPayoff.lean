/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseDecodedDebt
import Vegas.Game.RecoveryForeignExitBound
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
import GameTheory.Math.Probability.Bounds

/-! # Original phase payoff compared with physical debt-stopped values -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))

local notation "app" => phaseApplication (runtime setup) leaks

/-- The current genuine source residual already owes the focal source failure. -/
def PhaseOwesFailure (source : BehavioralProfile setup.program) (who : Player) :
    (app).ProtocolState → Prop
  | none => False
  | some control => RecoveryDecoded source (ProtocolState.OwesFailure who setup.program)
      control.execution.application.current

/-- Stop at actual physical exclusion or latent focal source debt. -/
def PhaseDebtStopped (source : BehavioralProfile setup.program) (who : Player)
    (state : (app).ProtocolState) : Prop :=
  (¬ ReactiveApplication.stateInvariant
    (fun state : PhaseRuntimeState (graph setup) => state.current.excluded = ∅) state) ∨
    PhaseOwesFailure setup leaks source who state

open Classical in
/-- The original phase payoff at ordinary endpoints and its existing floor at stops. -/
def phaseDebtStoppedPayoff {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program) (who : Player)
    (state : (app).ProtocolState) : ℝ :=
  if PhaseDebtStopped setup leaks source who state then excludedPayoff who else
    phaseExclusionBase setup .sequential (runtime setup) leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff state who

variable [Fintype Player]

open Classical in
/-- Original phase utility differs from its actual debt-stopped value only at
foreign physical exclusions before focal source debt. All whole-policy phase
continuations use the original phase completion contract. -/
theorem phase_expect_sub_debt_stopped_le_foreign_exit
    (plan : RuntimePhasePlan (graph setup))
    (singletons : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    (inputs : PMF (graph setup).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program)
    (menu : (app).ResponseMenu)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler)
    (certificate : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).BehavioralPolicy who)
    (who : Player) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (payoffBounded : ∀ history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History,
      |phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound)
    (start : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History) :
    let model := menu.information (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
    let stopped := model.runBehavioralUntil certificate players
      (fun history => PhaseDebtStopped setup leaks source who history.state) start
    |expect (model.runBehavioralTerminalFrom certificate players start)
        (fun final => phaseExclusionBase setup .sequential (runtime setup) leaks
          (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
            final.state who) -
      expect stopped (fun history => phaseDebtStoppedPayoff setup leaks parameter utility
        excludedPayoff source who history.state)| ≤
      (2 * bound) * (stopped.toOuterMeasure {history |
        PhaseDebtStopped setup leaks source who history.state ∧
        ¬ PhaseExcluded setup .sequential (runtime setup) leaks who history.state ∧
        ¬ PhaseOwesFailure setup leaks source who history.state}).toReal := by
  intro model stopped
  let payoff := fun history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History =>
    phaseExclusionBase setup .sequential (runtime setup) leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
        history.state who
  let continued := fun history =>
    expect (model.runBehavioralTerminalFrom certificate players history) payoff
  let value := fun history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History =>
    phaseDebtStoppedPayoff setup leaks parameter utility excludedPayoff source who history.state
  let foreign := {history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History | PhaseDebtStopped setup leaks source who history.state ∧
        ¬ PhaseExcluded setup .sequential (runtime setup) leaks who history.state ∧
        ¬ PhaseOwesFailure setup leaks source who history.state}
  have continuedBounded (history) : |continued history| ≤ bound :=
    expect_abs_le_of_bounded nonnegative payoffBounded
  have valueBounded (history) : |value history| ≤ bound := by
    dsimp only [value, phaseDebtStoppedPayoff]
    split_ifs
    · exact excludedBounded
    · exact payoffBounded history
  have continuedIntegrable : PayoffIntegrable stopped continued :=
    payoffIntegrable_of_bounded _ _ continuedBounded
  have valueIntegrable : PayoffIntegrable stopped value :=
    payoffIntegrable_of_bounded _ _ valueBounded
  have outside : ∀ history ∈ stopped.support, history ∉ foreign →
      continued history = value history := by
    intro history supported notForeign
    by_cases exited : PhaseDebtStopped setup leaks source who history.state
    · change continued history = if PhaseDebtStopped setup leaks source who history.state then
        excludedPayoff who else payoff history
      rw [ite_eq_left exited]
      by_cases own : PhaseExcluded setup .sequential (runtime setup) leaks who history.state
      · exact phase_excluded_expected_payoff setup .sequential (runtime setup) leaks _
          excludedPayoff
          menu (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler certificate players
          who history own
      · have owed : PhaseOwesFailure setup leaks source who history.state := by
          by_contra notOwed
          exact notForeign ⟨exited, own, notOwed⟩
        exact phase_owesFailure_expected_payoff setup leaks plan singletons inputs horizon scheduler
          parameter utility excludedPayoff menu completes certificate players who history
          (source := source) (by
            cases stateEq : history.state <;>
              simp only [PhaseOwesFailure, stateEq] at owed
            exact owed)
    · have ended := (model.mem_support_runBehavioralUntil certificate players
        (fun history => PhaseDebtStopped setup leaks source who history.state) start history
          supported).resolve_left exited
      change continued history = if PhaseDebtStopped setup leaks source who history.state then
        excludedPayoff who else payoff history
      rw [ite_eq_right exited]
      dsimp only [continued]
      rw [InformationModel.runBehavioralTerminalFrom,
        (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
          horizon scheduler).randomizedBackwardLaw_of_terminal (history := history) ended,
        expect_pure]
  have upper := expect_le_add_event_gap stopped foreign value continued (2 * bound)
    valueIntegrable continuedIntegrable
    (fun history supported outsideEvent => (outside history supported outsideEvent).le)
    (fun history _supported _insideEvent => by
      linarith [(abs_le.mp (continuedBounded history)).2, (abs_le.mp (valueBounded history)).1])
  have lower := expect_le_add_event_gap stopped foreign continued value (2 * bound)
    continuedIntegrable valueIntegrable
    (fun history supported outsideEvent => (outside history supported outsideEvent).symm.le)
    (fun history _supported _insideEvent => by
      linarith [(abs_le.mp (valueBounded history)).2, (abs_le.mp (continuedBounded history)).1])
  have decomposition : expect (model.runBehavioralTerminalFrom certificate players start) payoff =
      expect stopped continued := by
    rw [model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players
      (fun history => PhaseDebtStopped setup leaks source who history.state) start]
    exact expect_bind_tower stopped (model.runBehavioralTerminalFrom certificate players) payoff
      (payoffIntegrable_of_bounded _ payoff payoffBounded)
  change |expect (model.runBehavioralTerminalFrom certificate players start) payoff -
    expect stopped value| ≤ (2 * bound) * (stopped.toOuterMeasure foreign).toReal
  rw [decomposition]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Vegas
