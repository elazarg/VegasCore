/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryDecodedDebt
import GameTheoryExtensions.Analysis.Protocol.SourceGainTransport

/-! # Indifference after an owed recovery failure

Permanent exclusion and latent decoded debt both fix the owner's whole
continuation utility. The result applies to arbitrary whole-policy deviations,
and integrates over the actual assessment belief at an information site.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {profile : BehavioralProfile setup.program}
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  (menu : (recoveryApplication (runtime setup) leaks).ResponseMenu)
  (initial : PMF (RecoveryState (graph setup))) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
  (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)

local notation "recoveryN" => menu.information initial horizon scheduler

/-- At an excluded or indebted history, every whole-policy deviation has zero
gain under completion of the actual recovery runtime. -/
theorem recovery_historyGain_eq_zero_of_owes
    (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon scheduler)
    (assessment : (recoveryN).BehavioralAssessment) {who : Player}
    (deviation : (recoveryN).AssessmentDeviation who)
    (history : (recoveryN).InformationHistory who deviation.1.1)
    (owed : RecoveryExcluded (setup := setup) (leaks := leaks) who history.1.state ∨
      RecoveryDecodedState (leaks := leaks) profile
        (ProtocolState.OwesFailure who setup.program) history.1.state) :
    (recoveryN).historyGain ((recoveryN).runBehavioralTerminalFrom certificate)
      (fun final => final.state) (recoveryExclusionBase parameter utility excludedPayoff)
      assessment deviation history = 0 := by
  have fixed : ∀ players : ∀ player, (recoveryN).BehavioralPolicy player,
      expect (((recoveryN).runBehavioralTerminalFrom certificate players history.1).map
        (fun final => final.state)) (fun state =>
          recoveryExclusionBase parameter utility excludedPayoff state who) =
        excludedPayoff who := by
    intro players
    rw [expect_map]
    rcases owed with excluded | indebted
    · exact recovery_excluded_expect_exclusionBase parameter utility excludedPayoff menu initial
        horizon scheduler certificate players who history.1 excluded
    · exact recovery_owesFailure_expect_exclusionBase parameter utility excludedPayoff menu initial
        horizon scheduler completes certificate players who history.1 indebted
  unfold InformationModel.historyGain
  exact sub_eq_zero.mpr ((fixed _).trans (fixed _).symm)

/-- A belief supported on excluded or indebted histories makes the owner
indifferent among all whole-policy deviations at its actual information site. -/
theorem recovery_gain_eq_zero_of_owes
    [Finite (menu.protocol initial horizon scheduler).History]
    (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon scheduler)
    (assessment : (recoveryN).BehavioralAssessment) {who : Player}
    (deviation : (recoveryN).AssessmentDeviation who)
    (owed : ∀ history ∈ (assessment.belief who deviation.1).support,
      RecoveryExcluded (setup := setup) (leaks := leaks) who history.1.state ∨
        RecoveryDecodedState (leaks := leaks) profile
          (ProtocolState.OwesFailure who setup.program) history.1.state) :
    expect ((recoveryN).assessmentComparisonWith ((recoveryN).runBehavioralTerminalFrom certificate)
      (fun final => final.state) assessment who deviation).alternative
        (fun state => recoveryExclusionBase parameter utility excludedPayoff state who) -
      expect ((recoveryN).assessmentComparisonWith
        ((recoveryN).runBehavioralTerminalFrom certificate)
        (fun final => final.state) assessment who deviation).prescribed
        (fun state => recoveryExclusionBase parameter utility excludedPayoff state who) = 0 := by
  rw [(recoveryN).gain_eq_expect_historyGain]
  rw [expect_congr_on_support (g := fun _ => 0) (fun history supported =>
    recovery_historyGain_eq_zero_of_owes parameter utility excludedPayoff menu initial horizon
      scheduler certificate completes assessment deviation history (owed history supported))]
  exact expect_constant _ _

end Vegas
