/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.ExpectationMixture

/-! # Approximate comparison with source deviation gains

A target gain can be harmless on its own or bounded by a lottery of source
gains. Enlarging the common error and combining finitely many cases preserve
the same source gain function; no new assessment sequence is selected.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- A direct error bound or a source-deviation lottery bounds the target gain. -/
def GainComparison {α : Type*} (gain : ℝ) (sourceGain : α → ℝ) (error : ℝ) : Prop :=
  gain ≤ error ∨ ∃ mixture : PMF α, gain ≤ expect mixture sourceGain + error

/-- A comparison remains valid after enlarging its error. -/
theorem GainComparison.mono_error {α : Type*} {gain error enlarged : ℝ}
    {sourceGain : α → ℝ} (comparison : GainComparison gain sourceGain error)
    (covered : error ≤ enlarged) : GainComparison gain sourceGain enlarged := by
  rcases comparison with direct | ⟨mixture, compared⟩
  · exact Or.inl (direct.trans covered)
  · exact Or.inr ⟨mixture, compared.trans (add_le_add le_rfl covered)⟩

/-- Every case error fits the sum of the absolute errors of a finite family. -/
theorem GainComparison.sum_abs_errors {α ι : Type*} [Fintype ι]
    (errors : ι → ℝ) (selected : ι) {gain : ℝ} {sourceGain : α → ℝ}
    (comparison : GainComparison gain sourceGain (errors selected)) :
    GainComparison gain sourceGain (∑ index, |errors index|) := by
  have individual : |errors selected| ≤ ∑ index, |errors index| :=
    Finset.single_le_sum (f := fun index => |errors index|)
      (fun index _ => abs_nonneg (errors index)) (Finset.mem_univ selected)
  exact comparison.mono_error ((le_abs_self _).trans individual)

/-- A success-weighted source deviation is a genuine source lottery when a
zero-gain baseline is available. The source carrier need not be finite. -/
theorem GainComparison.of_weighted {α : Type*} (sourceGain : α → ℝ)
    (weight : Set.Icc (0 : ℝ) 1) (deviation baseline : α) (zero : sourceGain baseline = 0)
    {gain error : ℝ} (bounded : gain ≤ weight.val * sourceGain deviation + error) :
    GainComparison gain sourceGain error := by
  refine Or.inr ⟨mix weight.val weight.property.1 weight.property.2
    (PMF.pure deviation) (PMF.pure baseline), ?_⟩
  simpa only [expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
    expect_pure, zero, mul_zero, add_zero] using bounded

end GameTheory.Math.Probability
