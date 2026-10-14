/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.ProductMixture
import GameTheory.Math.Probability.ConditionalObservation

/-! # A common local product factor after observing the latent branch

Observation conditioning moves before the actual tagged draw kernel. Product
factors and a common selected coordinate are then needed only on the resulting
supported observation fiber.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- A shared local factor on a supported observation fiber is independent of
the complete latent branch and all remaining coordinates after conditioning. -/
theorem fiberPosterior_tagged_product_splitAt
    {Branch Index Observation : Type*} [Fintype Index] [DecidableEq Index]
    {A : Index → Type*} (law : PMF Branch) (draws : Branch → PMF ((index : Index) → A index))
    (observe : Branch → Observation) (observed : Observation)
    (present : observed ∈ (law.map observe).support)
    (factors : Branch → (index : Index) → PMF (A index))
    (product : ∀ branch ∈ (fiberPosterior law observe observed).support,
      draws branch = independentProduct (factors branch))
    (selected : Index) (common : PMF (A selected))
    (same : ∀ branch ∈ (fiberPosterior law observe observed).support,
      factors branch selected = common) :
    (fiberPosterior
      (law.bind fun branch => (draws branch).map (Prod.mk branch))
      (fun pair => observe pair.1) observed).map
        (fun pair => (pair.2 selected,
          (pair.1, fun index : {index // index ≠ selected} => pair.2 index))) =
      common.bind fun value =>
        ((fiberPosterior law observe observed).bind fun branch =>
          (independentProduct (fun index : {index // index ≠ selected} => factors branch index)).map
            fun rest => (branch, rest)).map fun residual => (value, residual) := by
  have shifted := fiberPosterior_bind_of_observation law
    (fun branch => (draws branch).map (Prod.mk branch)) observe (fun pair => observe pair.1)
      (by
        intro branch _ pair member
        obtain ⟨values, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        rfl) observed present
  rw [shifted, PMF.map_bind]
  calc
    _ = (fiberPosterior law observe observed).bind (fun branch =>
        (independentProduct (factors branch)).map fun values =>
          (values selected, (branch,
            fun index : {index // index ≠ selected} => values index))) := by
      apply bind_congr_on_support _
      intro branch supported
      rw [product branch supported, PMF.map_comp]
      rfl
    _ = _ := tagged_product_mixture_splitAt _ factors selected common same

end GameTheory.Math.Probability
