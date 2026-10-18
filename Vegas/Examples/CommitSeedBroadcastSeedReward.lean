/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastSeedIndependence

/-! # Survival and foreign-failure reward under the actual original seed law -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open scoped BigOperators
open GameTheory.Math.Probability

/-- The seed-determined reward event minus the own failure stake has positive
mean for every owner. Native survival and readout lemmas supply the payoff
comparison separately; this calculation uses the actual initialized seed law. -/
theorem nativeSeedLaw_survival_reward_expectation (owner : Fin 3) :
    expect nativeSeedLaw (fun seed => if seed.2 owner then
      if ∃ other : Fin 3, other ≠ owner ∧ seed.2 other = false then (1 : ℝ) else 0
      else -(3 / 2)) = 21 / 1000 := by
  classical
  rw [nativeSeedLaw, expect_map, expect_eq_sum, Fintype.sum_prod_type]
  simp_rw [callbackSeedLaw_atom]
  fin_cases owner <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
      Fin.exists_fin_succ, timingGood, goodCount]

end Vegas.Examples.CommitSeedBroadcast
