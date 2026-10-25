/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.OptionalDomination
import Mathlib.Probability.Distributions.Geometric

/-! # An infinite-support comparison without an attained payoff minimum

The reference is geometric on natural numbers. Its positive payoffs tend to
zero without attaining zero. The compared law keeps half of the reference and
otherwise fails with payoff minus one. Both actual payoff laws are integrable.
-/

noncomputable section

namespace GameTheoryExtensionsTests.OptionalDomination

open GameTheory.Math.Probability

private def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

private def reference : PMF ℕ := (ProbabilityTheory.geometricMeasure half).toPMF

private def payoff (number : ℕ) : ℝ := 1 / ((number : ℝ) + 1)

private def value (outcome : Option ℕ) : ℝ := outcome.elim (-1) payoff

private def law : PMF (Option ℕ) :=
  mix (1 / 2) (by norm_num) (by norm_num) (reference.map some) (PMF.pure none)

theorem reference_full_support (number : ℕ) : number ∈ reference.support := by
  rw [PMF.mem_support_iff]
  change ProbabilityTheory.geometricMeasure half {number} ≠ 0
  have halfNe : half ≠ 0 := by
    intro same
    have realSame := congrArg (fun value : unitInterval => (value : ℝ)) same
    norm_num [half] at realSame
  rw [ProbabilityTheory.geometricMeasure_singleton halfNe]
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  change (0 : ℝ) < (1 - (1 / 2 : ℝ)) ^ number * (1 / 2)
  positivity

private theorem payoff_positive (number : ℕ) : 0 < payoff number := by
  unfold payoff
  positivity

private theorem payoff_bounded (number : ℕ) : |payoff number| ≤ 1 := by
  rw [abs_of_pos (payoff_positive number)]
  unfold payoff
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (number : ℝ) + 1)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) number]

theorem reference_payoff_integrable : PayoffIntegrable reference payoff :=
  payoffIntegrable_of_bounded reference payoff payoff_bounded

theorem failed_law_integrable : PayoffIntegrable law value :=
  payoffIntegrable_of_bounded law value (C := 1) fun outcome => by
    cases outcome with
    | none => norm_num [value]
    | some number => exact payoff_bounded number

/-- Every reference payoff has a strictly smaller supported reference payoff. -/
theorem no_attained_minimum (number : ℕ) :
    ∃ next ∈ reference.support, payoff next < payoff number := by
  refine ⟨number + 1, reference_full_support _, ?_⟩
  unfold payoff
  apply one_div_lt_one_div_of_lt (by positivity)
  push_cast
  linarith

/-- The actual generic comparison applies to the infinite supported laws and
their integrability certificates, without selecting a minimum or floor. -/
theorem failure_does_not_improve : expect law value ≤ expect reference payoff := by
  exact expect_le_of_dominated_readout law reference id (by
    intro number
    rw [PMF.map_id, law, mix_apply,
      pmf_map_apply_of_injective _ (Option.some_injective ℕ)]
    simp only [PMF.pure_apply, Option.some_ne_none, ↓reduceIte, mul_zero, add_zero]
    exact mul_le_of_le_one_left zero_le (by norm_num)) value payoff
    failed_law_integrable reference_payoff_integrable (by
    intro outcome _ number reading
    change outcome = some number at reading
    subst outcome
    exact le_rfl) (by
    intro outcome _ reading number _
    change outcome = none at reading
    subst outcome
    exact (by norm_num : (-1 : ℝ) ≤ 0).trans (payoff_positive number).le)

end GameTheoryExtensionsTests.OptionalDomination
