/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Incentives

/-! # Transporting a deviation gain to a source deviation

The gain of a whole-policy deviation at an information site is the belief
expectation of its gain at each history of the site
(`GameTheory.Protocol.InformationModel.gain_eq_expect_historyGain`). So when a
map sends the histories of a site to those of a site of another model, the
gain at each history is at most the source gain at its image plus `δ`, the source
history gains are bounded by `R`, and the pushed-forward belief is within `β`
of the source belief in `ℓ¹`, the gain is at most the source gain plus
`δ + R * β` (`GameTheory.Protocol.InformationModel.gain_le_sourceGain_add`).
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} [DecidableEq ι] {E : ExecutionProtocol ι} (M : InformationModel E)
  {Observation : Type*}

/-- The gain of a whole-policy deviation at one history of its site: the
expected utility of the deviating policy minus that of the prescribed one,
continued by `run`. -/
def historyGain (run : M.ContinuationRunner) (observe : E.History → Observation)
    (utility : Observation → ι → ℝ) (assessment : M.BehavioralAssessment) {who : ι}
    (deviation : M.AssessmentDeviation who)
    (history : M.InformationHistory who deviation.1.1) : ℝ :=
  expect ((run (Profile.update (sig := M.behavioralSignature) assessment.strategy who
      deviation.2) history.1).map observe) (utility · who) -
    expect ((run (Profile.update (sig := M.behavioralSignature) assessment.strategy who
      (assessment.strategy who)) history.1).map observe) (utility · who)

/-- **The gain is the belief expectation of the history gains.** -/
theorem gain_eq_expect_historyGain [Finite E.History] (run : M.ContinuationRunner)
    (observe : E.History → Observation) (utility : Observation → ι → ℝ)
    (assessment : M.BehavioralAssessment) {who : ι} (deviation : M.AssessmentDeviation who) :
    expect (M.assessmentComparisonWith run observe assessment who deviation).alternative
        (utility · who) -
      expect (M.assessmentComparisonWith run observe assessment who deviation).prescribed
        (utility · who) =
      expect (assessment.belief who deviation.1)
        (M.historyGain run observe utility assessment deviation) := by
  simp only [assessmentComparisonWith, assessmentLawWith, expect_map]
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
    ← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  refine expect_congr_on_support fun history _ => ?_
  simp only [historyGain, expect_map]

variable {E' : ExecutionProtocol ι} {N : InformationModel E'} {Observation' : Type*}

/-- **A gain near a source gain.** If a map sends the histories of a deviation's
site to those of a source deviation's site, each history gain is at most the
source history gain at its image plus `δ`, and the source history gains are bounded
by `R`, then the gain is at most the source gain plus `δ` plus `R` times the
`ℓ¹` distance of the pushed-forward belief from the source belief. -/
theorem gain_le_sourceGain_add [Finite E.History] [Finite E'.History]
    (run : M.ContinuationRunner) (observe : E.History → Observation)
    (utility : Observation → ι → ℝ) (assessment : M.BehavioralAssessment)
    (sourceRun : N.ContinuationRunner) (sourceObserve : E'.History → Observation')
    (sourceUtility : Observation' → ι → ℝ) (source : N.BehavioralAssessment) {who : ι}
    (deviation : M.AssessmentDeviation who) (sourceDeviation : N.AssessmentDeviation who)
    [Fintype (N.InformationHistory who sourceDeviation.1.1)]
    (project : M.InformationHistory who deviation.1.1 →
      N.InformationHistory who sourceDeviation.1.1)
    (δ R : ℝ)
    (close : ∀ history ∈ (assessment.belief who deviation.1).support,
      M.historyGain run observe utility assessment deviation history ≤
        N.historyGain sourceRun sourceObserve sourceUtility source sourceDeviation
          (project history) + δ)
    (bounded : ∀ point,
      |N.historyGain sourceRun sourceObserve sourceUtility source sourceDeviation point| ≤ R) :
    expect (M.assessmentComparisonWith run observe assessment who deviation).alternative
        (utility · who) -
      expect (M.assessmentComparisonWith run observe assessment who deviation).prescribed
        (utility · who) ≤
      (expect (N.assessmentComparisonWith sourceRun sourceObserve source who
          sourceDeviation).alternative (sourceUtility · who) -
        expect (N.assessmentComparisonWith sourceRun sourceObserve source who
          sourceDeviation).prescribed (sourceUtility · who)) +
        δ + R * ∑ point, |(((assessment.belief who deviation.1).map project) point).toReal -
          ((source.belief who sourceDeviation.1) point).toReal| := by
  rw [M.gain_eq_expect_historyGain run observe utility assessment deviation,
    N.gain_eq_expect_historyGain sourceRun sourceObserve sourceUtility source sourceDeviation]
  set gain := M.historyGain run observe utility assessment deviation
  set sourceGain := N.historyGain sourceRun sourceObserve sourceUtility source sourceDeviation
  have nearImage : expect (assessment.belief who deviation.1) gain ≤
      expect ((assessment.belief who deviation.1).map project) sourceGain + δ := by
    rw [expect_map]
    have shifted := expect_mono (μ := assessment.belief who deviation.1)
      (f := gain) (g := fun history => sourceGain (project history) + δ)
      (fun history member => close history member)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    rwa [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
      expect_constant] at shifted
  have transport : expect ((assessment.belief who deviation.1).map project) sourceGain -
      expect (source.belief who sourceDeviation.1) sourceGain ≤
      R * ∑ point, |(((assessment.belief who deviation.1).map project) point).toReal -
        ((source.belief who sourceDeviation.1) point).toReal| := by
    rw [expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun point _ => ?_
    rw [← sub_mul]
    calc _ ≤ |((((assessment.belief who deviation.1).map project) point).toReal -
            ((source.belief who sourceDeviation.1) point).toReal) * sourceGain point| :=
          le_abs_self _
      _ = |(((assessment.belief who deviation.1).map project) point).toReal -
            ((source.belief who sourceDeviation.1) point).toReal| * |sourceGain point| :=
          abs_mul _ _
      _ ≤ _ := by
          rw [mul_comm R]
          exact mul_le_mul_of_nonneg_left (bounded point) (abs_nonneg _)
  linarith

end GameTheory.Protocol.InformationModel
