/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Mixture
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Products of bounded independent private likelihoods -/

noncomputable section

namespace GameTheory.Math.Probability

/-- Independent original private tags factor the product of their bounded
nonnegative likelihoods. The tags may have arbitrary infinite memory types. -/
theorem expect_independentProduct_prod {Index : Type} [Fintype Index]
    {Memory : Index → Type} (laws : (index : Index) → PMF (Memory index))
    (payoff : (index : Index) → Memory index → ℝ)
    (nonnegative : ∀ index memory, 0 ≤ payoff index memory)
    (bounded : ∀ index memory, payoff index memory ≤ 1) :
    expect (independentProduct laws) (fun memories => ∏ index, payoff index (memories index)) =
      ∏ index, expect (laws index) (payoff index) := by
  let test := fun index memory => mix (payoff index memory) (nonnegative index memory)
    (bounded index memory) (PMF.pure true) (PMF.pure false)
  have atom (index) (memory : Memory index) : (test index memory true).toReal =
      payoff index memory := by
    simp [test, nonnegative index memory]
  have equality := congrArg (fun law : PMF (Index → Bool) =>
    (law (fun _ => true)).toReal) (independentProduct_bind laws test)
  simpa only [toReal_bind_apply, independentProduct_apply, ENNReal.toReal_prod, atom] using equality

end GameTheory.Math.Probability
