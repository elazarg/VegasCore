/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheory.Math.Probability.Bounds

/-! # Only foreign first exclusions contribute continuation error

At an own exclusion every whole continuation already pays the exclusion utility.
The stopped comparison assigns that utility to every exit; its discrepancy is
therefore confined to first exits that exclude only other owners.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A genuine recovery endpoint with at least one permanent public exclusion. -/
def RecoveryPublicExclusion :
    (recoveryApplication (runtime setup) leaks).ProtocolState → Prop
  | none => False
  | some control => control.execution.application.excluded ≠ ∅

open Classical in
/-- Relative to one owner, the first-exclusion continuation error is bounded
only by the mass of exits that do not exclude that owner. This holds for every
actual response menu and arbitrary later whole-policy behavior. -/
theorem recovery_expect_sub_stopped_le_foreign_exit {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (recoveryApplication (runtime setup) leaks).ResponseMenu)
    (initial : PMF (recoveryApplication (runtime setup) leaks).State) (horizon : Nat)
    (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (payoffBounded : ∀ state : (recoveryApplication (runtime setup) leaks).ProtocolState,
      |recoveryExclusionBase parameter utility excludedPayoff state who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound)
    (start : (menu.protocol initial horizon scheduler).History) :
    let model := menu.information initial horizon scheduler
    let stop := fun history : (menu.protocol initial horizon scheduler).History =>
      RecoveryPublicExclusion (setup := setup) (leaks := leaks) history.state
    let stopped := model.runBehavioralUntil certificate players stop start
    |expect (model.runBehavioralTerminalFrom certificate players start)
        (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state who) -
      expect stopped (fun history => if stop history then excludedPayoff who else
        recoveryExclusionBase parameter utility excludedPayoff history.state who)| ≤
      (2 * bound) * (stopped.toOuterMeasure {history | stop history ∧
        ¬ RecoveryExcluded (setup := setup) (leaks := leaks) who history.state}).toReal := by
  classical
  intro model stop stopped
  let payoff := fun history : (menu.protocol initial horizon scheduler).History =>
    recoveryExclusionBase parameter utility excludedPayoff history.state who
  let continued := fun history : (menu.protocol initial horizon scheduler).History =>
    expect (model.runBehavioralTerminalFrom certificate players history) payoff
  let value := fun history => if stop history then excludedPayoff who else payoff history
  let foreign := {history : (menu.protocol initial horizon scheduler).History |
    stop history ∧ ¬ RecoveryExcluded (setup := setup) (leaks := leaks) who history.state}
  have continuedBounded (history) : |continued history| ≤ bound :=
    expect_abs_le_of_bounded nonnegative (fun final => payoffBounded final.state)
  have valueBounded (history) : |value history| ≤ bound := by
    dsimp only [value]
    split_ifs
    · exact excludedBounded
    · exact payoffBounded history.state
  have continuedIntegrable : PayoffIntegrable stopped continued :=
    payoffIntegrable_of_bounded _ _ continuedBounded
  have valueIntegrable : PayoffIntegrable stopped value :=
    payoffIntegrable_of_bounded _ _ valueBounded
  have outside : ∀ history ∈ stopped.support, history ∉ foreign →
      continued history = value history := by
    intro history supported notForeign
    by_cases exited : stop history
    · have own : RecoveryExcluded (setup := setup) (leaks := leaks) who history.state := by
        by_contra absent
        exact notForeign ⟨exited, absent⟩
      change continued history = if stop history then excludedPayoff who else payoff history
      rw [ite_eq_left exited]
      exact recovery_excluded_expect_exclusionBase parameter utility excludedPayoff menu initial
        horizon scheduler certificate players who history own
    · have terminal := model.mem_support_runBehavioralUntil certificate players stop start history
        supported
      have ended := terminal.resolve_left exited
      change continued history = if stop history then excludedPayoff who else payoff history
      rw [ite_eq_right exited]
      dsimp only [continued]
      rw [InformationModel.runBehavioralTerminalFrom,
        (menu.protocol initial horizon scheduler).randomizedBackwardLaw_of_terminal
          (history := history) ended, expect_pure]
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
  have decomposition :
      expect (model.runBehavioralTerminalFrom certificate players start) payoff =
        expect stopped continued := by
    rw [model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players stop start]
    exact expect_bind_tower stopped (model.runBehavioralTerminalFrom certificate players) payoff
      (payoffIntegrable_of_bounded _ payoff (fun final => payoffBounded final.state))
  change |expect (model.runBehavioralTerminalFrom certificate players start) payoff -
    expect stopped value| ≤ (2 * bound) * (stopped.toOuterMeasure foreign).toReal
  rw [decomposition]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Vegas
