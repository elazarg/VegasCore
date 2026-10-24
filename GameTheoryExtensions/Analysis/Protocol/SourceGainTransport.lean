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

/-- A payoff fixed on every continuation support leaves no profitable or costly
whole-policy deviation at the starting history. The constant may depend on that
history; no information or independence assumption is needed. -/
theorem historyGain_eq_zero_of_constant_payoff (run : M.ContinuationRunner)
    (observe : E.History → Observation) (utility : Observation → ι → ℝ)
    (assessment : M.BehavioralAssessment) {who : ι}
    (deviation : M.AssessmentDeviation who)
    (history : M.InformationHistory who deviation.1.1) (value : ℝ)
    (constant : ∀ players final, final ∈ (run players history.1).support →
      utility (observe final) who = value) :
    M.historyGain run observe utility assessment deviation history = 0 := by
  have fixed (players : ∀ owner, M.BehavioralPolicy owner) :
      expect ((run players history.1).map observe) (utility · who) = value := by
    rw [expect_map]
    calc
      _ = expect (run players history.1) (fun _ => value) :=
        expect_congr_on_support (fun final supported => constant players final supported)
      _ = value := expect_constant _ _
  exact sub_eq_zero.mpr ((fixed _).trans (fixed _).symm)

/-- Continuation indifference at every hidden history gives indifference at the
information site for any assessment beliefs. Different hidden histories may
have different fixed payoffs; only control over the continuation is irrelevant. -/
theorem gain_eq_zero_of_constant_continuations [Finite E.History]
    (run : M.ContinuationRunner) (observe : E.History → Observation)
    (utility : Observation → ι → ℝ) (assessment : M.BehavioralAssessment) {who : ι}
    (deviation : M.AssessmentDeviation who)
    (value : M.InformationHistory who deviation.1.1 → ℝ)
    (constant : ∀ history players final, final ∈ (run players history.1).support →
      utility (observe final) who = value history) :
    expect (M.assessmentComparisonWith run observe assessment who deviation).alternative
        (utility · who) -
      expect (M.assessmentComparisonWith run observe assessment who deviation).prescribed
        (utility · who) = 0 := by
  rw [M.gain_eq_expect_historyGain]
  calc
    _ = expect (assessment.belief who deviation.1) (fun _ => 0) :=
      expect_congr_on_support (fun history _ =>
        M.historyGain_eq_zero_of_constant_payoff run observe utility assessment deviation
          history (value history) (constant history))
    _ = 0 := expect_constant _ _

end GameTheory.Protocol.InformationModel
