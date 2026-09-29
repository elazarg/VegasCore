/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.IncentiveCone

/-! # Incentive comparisons between integrable laws

An incentive comparison compares extended-real expectations. When both laws
give the payoff a finite expectation, it is the comparison of the real
expectations, whatever the outcome carrier.
-/

namespace GameTheory.IncentiveComparison

open Math.Probability

variable {Outcome : Type*}

theorem holds_iff_of_integrable (comparison : IncentiveComparison Outcome)
    (utility : Outcome → ℝ) (prescribed : PayoffIntegrable comparison.prescribed utility)
    (alternative : PayoffIntegrable comparison.alternative utility) :
    comparison.Holds utility ↔
      expect comparison.alternative utility ≤ expect comparison.prescribed utility :=
  euPreference_iff (fun outcome (_ : Unit) => utility outcome) () _ _ prescribed alternative

end GameTheory.IncentiveComparison
