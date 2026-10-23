/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Analysis.Protocol.Incentives

/-! # The gain of a deviation at one history

`GameTheory.Protocol.InformationModel.historyGain` is the gain of a whole-policy
deviation at one history of its information site. The gain at the site is the
belief expectation of these history gains
(`GameTheory.Protocol.InformationModel.gain_eq_expect_historyGain`).
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

end GameTheory.Protocol.InformationModel
