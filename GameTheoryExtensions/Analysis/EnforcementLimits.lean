/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Enforcement

/-! # When sufficiently large finite sanctions work

For a finite family of continuation comparisons, arbitrarily large sanctions
work exactly when no deviation reduces collection probability and every
deviation with unchanged collection probability is already unprofitable.
The relevant quantity is additional collection probability, so an already
inevitable one-time sanction cannot deter a later profitable deviation.

This is a real-utility characterization. It does not introduce infinite
utilities or construct consistent beliefs. To use it for sequential equilibrium,
the family must cover all continuation deviations at all information sets of
one consistent assessment. Finiteness of a test family is a substantive premise.
-/

noncomputable section

namespace GameTheory.Enforcement

open Math.Probability

variable {Outcome Index : Type*}

/-- The utility gain is offset precisely by the increase in collection risk. -/
theorem holds_iff_incremental_sanction (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ) :
    comparison.Holds (sanctionedUtility base sanction penalty) ↔
      comparison.alternative.expect base - comparison.prescribed.expect base ≤
        (comparison.alternative.probOf sanction - comparison.prescribed.probOf sanction) *
          penalty := by
  rw [IncentiveComparison.Holds, ← sub_nonpos, regret_eq]
  exact sub_nonpos

/-- A decrease in collection risk eventually outweighs any fixed base loss. -/
theorem incremental_nonneg_of_eventually_deters (gain increment cutoff : ℝ)
    (deters : ∀ penalty, cutoff ≤ penalty → gain ≤ increment * penalty) :
    0 ≤ increment := by
  by_contra negative
  have negative : increment < 0 := lt_of_not_ge negative
  have bound := deters (max cutoff ((gain - 1) / increment)) (le_max_left ..)
  have upper := mul_le_mul_of_nonpos_left
    (le_max_right cutoff ((gain - 1) / increment)) negative.le
  have cancel : increment * ((gain - 1) / increment) = gain - 1 := by
    field_simp [ne_of_lt negative]
  rw [cancel] at upper
  linarith

/-- For a finite comparison family, eventual deterrence by one common sanction
is exactly nonnegative incremental collection and no profitable undetectable
comparison. The prescribed plan may itself already face collection. -/
theorem exists_uniform_sanction_iff [Finite Index]
    (comparisons : Index → IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) :
    (∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ penalty, cutoff ≤ penalty → ∀ index,
      (comparisons index).Holds (sanctionedUtility base sanction penalty)) ↔
    ∀ index,
      0 ≤ (comparisons index).alternative.probOf sanction -
        (comparisons index).prescribed.probOf sanction ∧
      ((comparisons index).alternative.probOf sanction =
          (comparisons index).prescribed.probOf sanction →
        (comparisons index).Holds base) := by
  classical
  let _ := Fintype.ofFinite Index
  constructor
  · rintro ⟨cutoff, _, deters⟩ index
    have bound (penalty : ℝ) (large : cutoff ≤ penalty) :=
      (holds_iff_incremental_sanction (comparisons index) base sanction penalty).mp
        (deters penalty large index)
    refine ⟨incremental_nonneg_of_eventually_deters _ _ cutoff bound, ?_⟩
    intro equal
    have atCutoff := bound cutoff le_rfl
    rw [equal, sub_self, zero_mul] at atCutoff
    exact sub_nonpos.mp atCutoff
  · intro condition
    let gain (index : Index) :=
      (comparisons index).alternative.expect base - (comparisons index).prescribed.expect base
    let increment (index : Index) :=
      (comparisons index).alternative.probOf sanction -
        (comparisons index).prescribed.probOf sanction
    let amount (index : Index) := max 0 (gain index / increment index)
    let cutoff := ∑ index, amount index
    have amount_nonneg (index : Index) : 0 ≤ amount index := le_max_left ..
    refine ⟨cutoff, Finset.sum_nonneg (fun index _ => amount_nonneg index), ?_⟩
    intro penalty large index
    rw [holds_iff_incremental_sanction]
    change gain index ≤ increment index * penalty
    have nonnegative : 0 ≤ increment index := (condition index).1
    by_cases zero : increment index = 0
    · have equal : (comparisons index).alternative.probOf sanction =
          (comparisons index).prescribed.probOf sanction := sub_eq_zero.mp zero
      have noGain := (condition index).2 equal
      rw [zero, zero_mul]
      exact sub_nonpos.mpr noGain
    · have positive : 0 < increment index := lt_of_le_of_ne nonnegative (Ne.symm zero)
      have bound : gain index / increment index ≤ penalty :=
        (le_max_right _ _).trans
          ((Finset.single_le_sum (fun entry _ => amount_nonneg entry)
            (Finset.mem_univ index)).trans large)
      exact (div_le_iff₀ positive).mp bound |>.trans_eq (mul_comm _ _)

/-- A sanction cannot repair a profitable comparison with unchanged risk,
regardless of its magnitude. This includes a binary charge already certain. -/
theorem not_holds_of_equal_collection (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ)
    (equal : comparison.alternative.probOf sanction = comparison.prescribed.probOf sanction)
    (profitable : comparison.prescribed.expect base < comparison.alternative.expect base) :
    ¬ comparison.Holds (sanctionedUtility base sanction penalty) := by
  rw [holds_iff_incremental_sanction, equal, sub_self, zero_mul]
  exact not_le.mpr (sub_pos.mpr profitable)

/-- A finite pure-comparison certificate also covers mixtures of those
comparisons. Its application to behavioral deviations requires a separate
realization theorem identifying their conditional outcome laws. -/
theorem holds_mixture (comparisons : Index → IncentiveComparison Outcome)
    (weights : FinDist Index) (utility : Outcome → ℝ)
    (holds : ∀ index ∈ weights.support, (comparisons index).Holds utility) :
    (IncentiveComparison.mk
      (weights.bind (fun index => (comparisons index).prescribed))
      (weights.bind (fun index => (comparisons index).alternative))).Holds utility := by
  simp only [IncentiveComparison.Holds, FinDist.expect_bind]
  exact FinDist.expect_mono holds

/-- A first-departure comparison scales both its possible gain and its added
collection risk by the probability of departing. Thus arbitrarily rare mixed
departures do not require unbounded fines when detection is conditional on the
departure. The probabilistic coupling establishing these two bounds is external. -/
theorem holds_of_departure_bound (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome)
    (departure gain detection penalty : ℝ)
    (departure_nonnegative : 0 ≤ departure) (penalty_nonnegative : 0 ≤ penalty)
    (gain_bound : comparison.alternative.expect base - comparison.prescribed.expect base ≤
      departure * gain)
    (collection_bound : departure * detection ≤
      comparison.alternative.probOf sanction - comparison.prescribed.probOf sanction)
    (sufficient : gain ≤ detection * penalty) :
    comparison.Holds (sanctionedUtility base sanction penalty) := by
  rw [holds_iff_incremental_sanction]
  calc
    _ ≤ departure * gain := gain_bound
    _ ≤ departure * (detection * penalty) :=
      mul_le_mul_of_nonneg_left sufficient departure_nonnegative
    _ = (departure * detection) * penalty := (mul_assoc ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right collection_bound penalty_nonnegative

/-- Pointwise positive detection in an infinite family does not supply one
finite uniform fine: these tests have unit gain and detection tending to zero. -/
theorem no_uniform_sanction_for_vanishing_detection :
    ¬ ∃ penalty : ℝ, ∀ index : ℕ, (1 : ℝ) ≤ (1 / (index + 1 : ℝ)) * penalty := by
  rintro ⟨penalty, deters⟩
  obtain ⟨index, larger⟩ := exists_nat_gt penalty
  have positive : (0 : ℝ) < index + 1 := by positivity
  have bound := deters index
  rw [one_div_mul_eq_div, le_div_iff₀ positive, one_mul] at bound
  linarith

end GameTheory.Enforcement
