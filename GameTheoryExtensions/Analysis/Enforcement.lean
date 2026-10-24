/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.Bounds
import GameTheoryExtensions.Math.Probability.Support

/-! # Deterrence by probabilistic sanctions

A sanction subtracts a fixed amount of utility on a specified event. For a
comparison with an unsanctioned feasible plan, a gain bound `G` and a detection
probability lower bound `p` give regret at most `G - p * penalty`.

The probability and gain bounds concern the actual compared laws. Applied at
an information set, they are conditional on that assessment's beliefs. No
monitor, evidence, collection mechanism, or sequentially consistent belief
system is constructed here. Sanctions are measured in utility, not currency.

For a randomized alarm observing a PMF on any carrier, the largest detection
probability compatible with zero false positives is exactly the deviating
law's mass outside the lawful support. This concerns the specified observable
law. A compiler preserving all source-compatible strategies needs soundness
for each permitted source strategy, not only one equilibrium profile.
-/

noncomputable section

namespace GameTheory

open Math.Probability

namespace Enforcement

variable {Outcome : Type*}

/-- Zero false positives require the alarm to stay silent at every observation
with positive lawful probability, even when the alarm itself randomizes. -/
theorem alarm_zero_iff (lawful : PMF Outcome) (alarm : Outcome → PMF Bool) :
    ((lawful.bind alarm) true).toReal = 0 ↔
      ∀ outcome ∈ lawful.support, ((alarm outcome) true).toReal = 0 := by
  simp only [pmf_toReal_eq_zero_iff, PMF.mem_support_bind_iff]
  constructor
  · intro silent outcome supported reported
    exact silent ⟨outcome, supported, reported⟩
  · rintro silent ⟨outcome, supported, reported⟩
    exact silent outcome supported reported

/-- If every deviating observation is also lawful, zero false positives force
zero detection, even when the two observation laws have different probabilities. -/
theorem alarm_zero_of_support_subset (lawful deviating : PMF Outcome)
    (included : deviating.support ⊆ lawful.support) (alarm : Outcome → PMF Bool)
    (no_false_positives : ((lawful.bind alarm) true).toReal = 0) :
    ((deviating.bind alarm) true).toReal = 0 := by
  apply (alarm_zero_iff deviating alarm).mpr
  intro outcome supported
  exact (alarm_zero_iff lawful alarm).mp no_false_positives outcome (included supported)

/-- The deterministic alarm fires exactly outside the admitted observations. -/
def outsideAlarm (admitted : Set Outcome) (outcome : Outcome) : PMF Bool := by
  classical
  exact PMF.pure (if outcome ∈ admitted then false else true)

open Classical in
@[simp] theorem outsideAlarm_true (admitted : Set Outcome) (outcome : Outcome) :
    ((outsideAlarm admitted outcome) true).toReal =
      if outcome ∈ admitted then 0 else 1 := by
  classical
  by_cases member : outcome ∈ admitted <;> simp [outsideAlarm, member, PMF.pure_apply]

/-- Every alarm silent on admitted observations detects at most the law's
mass outside that set, even if the alarm randomizes. -/
theorem alarm_detection_le_outside_mass (law : PMF Outcome) (admitted : Set Outcome)
    (alarm : Outcome → PMF Bool)
    (sound : ∀ outcome ∈ admitted, ((alarm outcome) true).toReal = 0) :
    ((law.bind alarm) true).toReal ≤ (law.toOuterMeasure admittedᶜ).toReal := by
  classical
  rw [toReal_bind_apply, ← expect_indicator]
  refine expect_mono (fun outcome _ => ?_)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun outcome => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact pmf_toReal_apply_le_one _ _)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun outcome => by split <;> norm_num)
  by_cases member : outcome ∈ admitted
  · simp [member, sound outcome member]
  · simpa [member] using pmf_toReal_apply_le_one (alarm outcome) true

/-- The deterministic outside-set alarm attains the upper bound on sound
detection. Its silence holds on the entire admitted set, not just one law. -/
theorem outsideAlarm_detection (law : PMF Outcome) (admitted : Set Outcome) :
    ((law.bind (outsideAlarm admitted)) true).toReal =
      (law.toOuterMeasure admittedᶜ).toReal := by
  classical
  rw [toReal_bind_apply, ← expect_indicator]
  apply congrArg (expect law)
  funext outcome
  by_cases member : outcome ∈ admitted <;> simp [member]

end Enforcement
end GameTheory
