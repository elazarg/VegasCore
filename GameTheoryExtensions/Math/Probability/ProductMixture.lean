/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Support

/-! # A common coordinate of a tagged product mixture

A coordinate whose conditional product factor is the same on every supported
branch is independent of both the branch and every remaining coordinate.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- A common product coordinate factors out of a latent mixture while keeping
the complete latent branch and all other sampled coordinates. -/
theorem tagged_product_mixture_splitAt
    {Branch Index : Type*} [Fintype Index] [DecidableEq Index]
    {A : Index → Type*} (law : PMF Branch) (kernel : Branch → (index : Index) → PMF (A index))
    (selected : Index) (common : PMF (A selected))
    (same : ∀ branch ∈ law.support, kernel branch selected = common) :
    (law.bind fun branch => (independentProduct (kernel branch)).map fun values =>
      (values selected, (branch, fun index : {index // index ≠ selected} => values index))) =
      common.bind fun value =>
        (law.bind fun branch =>
          (independentProduct (fun index : {index // index ≠ selected} => kernel branch index)).map
            fun rest => (branch, rest)).map fun residual => (value, residual) := by
  classical
  let split := Equiv.piSplitAt selected A
  calc
    _ = law.bind (fun branch => common.bind fun value =>
        (independentProduct (fun index : {index // index ≠ selected} => kernel branch index)).map
          fun rest => (value, (branch, rest))) := by
      apply bind_congr_on_support _
      intro branch supported
      change (independentProduct (kernel branch)).map
        ((fun parts => (parts.1, (branch, parts.2))) ∘ split) = _
      rw [independentProduct_splitAt _ selected, same branch supported]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      apply bind_congr_on_support _
      intro value _
      apply map_congr_on_support
      intro rest _
      change ((split (split.symm (value, rest))).1,
        (branch, (split (split.symm (value, rest))).2)) = _
      rw [split.apply_symm_apply]
    _ = _ := by
      rw [PMF.bind_comm]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

end GameTheory.Math.Probability
