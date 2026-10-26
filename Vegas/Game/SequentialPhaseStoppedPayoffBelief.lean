/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseStoppedPayoff
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Belief averages of original phase debt-stopped utility -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))

local notation "app" => phaseApplication runtime leaks

variable [Fintype Player]

open Classical in
/-- Every belief average of original phase continuation error is controlled by
its actual foreign-exit mass. No finiteness of the belief support is required. -/
theorem phase_belief_expect_abs_sub_debt_stopped_le_foreign_exit
    (plan : RuntimePhasePlan (graph setup))
    (singletons : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    (inputs : PMF (graph setup).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program)
    (menu : (app).ResponseMenu)
    (completes : PhaseService.CompletesPlay runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler)
    (certificate : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).BehavioralPolicy who)
    (who : Player) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (payoffBounded : ∀ history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History,
      |phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound)
    (belief : PMF (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History) :
    let model := menu.information (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
    let kernel := model.runBehavioralUntil certificate players
      (fun history => PhaseDebtStopped setup runtime leaks source who history.state)
    let foreign := {history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
        horizon scheduler).History |
      PhaseDebtStopped setup runtime leaks source who history.state ∧
        ¬ PhaseExcluded setup .sequential runtime leaks who history.state ∧
        ¬ PhaseOwesFailure setup runtime leaks source who history.state}
    expect belief (fun history =>
      |expect (model.runBehavioralTerminalFrom certificate players history)
          (fun final => phaseExclusionBase setup .sequential runtime leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
              final.state who) -
        expect (kernel history) (fun final => phaseDebtStoppedPayoff setup runtime leaks parameter
          utility
          excludedPayoff source who final.state)|) ≤
      (2 * bound) * ((belief.bind kernel).toOuterMeasure foreign).toReal := by
  intro model kernel foreign
  let payoff := fun history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History =>
    phaseExclusionBase setup .sequential runtime leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
        history.state who
  let read := fun history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History =>
    phaseDebtStoppedPayoff setup runtime leaks parameter utility excludedPayoff source who
      history.state
  let error := fun history =>
    |expect (model.runBehavioralTerminalFrom certificate players history) payoff -
      expect (kernel history) read|
  let mass := fun history => ((kernel history).toOuterMeasure foreign).toReal
  have readBounded (history) : |read history| ≤ bound := by
    dsimp only [read, phaseDebtStoppedPayoff]
    split_ifs
    · exact excludedBounded
    · exact payoffBounded history
  have errorBounded (history) : |error history| ≤ 2 * bound := by
    dsimp only [error]
    rw [abs_abs]
    exact (abs_sub _ _).trans (by
      linarith [expect_abs_le_of_bounded nonnegative payoffBounded
          (μ := model.runBehavioralTerminalFrom certificate players history),
        expect_abs_le_of_bounded nonnegative readBounded (μ := kernel history)])
  have pointwise (history) : error history ≤ (2 * bound) * mass history :=
    phase_expect_sub_debt_stopped_le_foreign_exit setup runtime leaks plan singletons inputs horizon
      scheduler parameter utility excludedPayoff source menu completes certificate players who
        nonnegative payoffBounded excludedBounded history
  have averaged := expect_mono (fun history _ => pointwise history)
    (payoffIntegrable_of_bounded belief error errorBounded)
    (payoffIntegrable_const_mul (payoffIntegrable_toReal_toOuterMeasure belief kernel foreign))
  rw [expect_const_mul] at averaged
  refine averaged.trans (le_of_eq (congrArg (fun value => (2 * bound) * value) ?_))
  let indicator := fun history => @ite ℝ (history ∈ foreign) (Classical.propDecidable _) 1 0
  have inner : mass = fun history => expect (kernel history) indicator := by
    funext history
    exact (expect_indicator (kernel history) foreign).symm
  have indicatorBounded : ∀ history, |indicator history| ≤ 1 := fun history => by
    dsimp only [indicator]
    split <;> norm_num
  rw [inner, ← expect_bind_tower_bounded belief kernel indicator indicatorBounded]
  exact expect_indicator (belief.bind kernel) foreign

end Vegas
