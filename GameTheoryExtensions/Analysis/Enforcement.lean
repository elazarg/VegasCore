/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Analysis.IncentiveCone
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Deterrence by probabilistic sanctions

A sanction subtracts a fixed amount of utility on a specified event. For a
comparison with an unsanctioned feasible plan, a gain bound `G` and a detection
probability lower bound `p` give regret at most `G - p * penalty`.

The probability and gain bounds concern the actual compared laws. Applied at
an information set, they are conditional on that assessment's beliefs. No
monitor, evidence, collection mechanism, or sequentially consistent belief
system is constructed here. Sanctions are measured in utility, not currency.

For a randomized alarm observing a finite-support law, the largest detection
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

end Enforcement
end GameTheory
