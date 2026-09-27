/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Convergence

/-! # Deferring a binary choice through finitely many opportunities

A timing law conditional on choosing true induces behavioral hazards. Their
survival products recover the original choice probability exactly. This is
probability algebra, not a game interpreter or an equilibrium assertion.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

open Filter

variable {slots : Nat}

theorem bind_bool_mix {α : Type} (choice : FinDist Bool)
    (opening waiting : FinDist α) :
    (choice.bind fun disclose => if disclose then opening else waiting) =
      FinDist.mix (choice.prob true) (choice.prob_nonneg true) (choice.prob_le_one true)
        opening waiting := by
  have total := choice.sum_prob
  simp only [Fintype.sum_bool] at total
  have complement : choice.prob false = 1 - choice.prob true := by linarith
  apply FinDist.ext_of_prob
  intro action
  rw [FinDist.prob_bind, FinDist.expect_eq_sum, Fintype.sum_bool, FinDist.prob_mix]
  simp only [Bool.false_eq_true, ↓reduceIte, complement]

/-- Mass assigned to sending strictly before an opportunity. -/
def timingPrefix (timing : FinDist (Fin slots)) (count : Nat) : ℝ :=
  ∑ slot : Fin slots, if slot.val < count then timing.prob slot else 0

theorem timingPrefix_nonnegative (timing : FinDist (Fin slots)) (count : Nat) :
    0 ≤ timing.timingPrefix count := by
  apply Finset.sum_nonneg
  intro slot _
  split
  · exact timing.prob_nonneg slot
  · exact le_rfl

theorem timingPrefix_le_one (timing : FinDist (Fin slots)) (count : Nat) :
    timing.timingPrefix count ≤ 1 := by
  rw [← timing.sum_prob]
  apply Finset.sum_le_sum
  intro slot _
  split
  · exact le_rfl
  · exact timing.prob_nonneg slot

theorem timingPrefix_mix (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1)
    (first second : FinDist (Fin slots)) (count : Nat) :
    (mix weight nonnegative bounded first second).timingPrefix count =
      weight * first.timingPrefix count + (1 - weight) * second.timingPrefix count := by
  unfold timingPrefix
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro slot _
  by_cases before : slot.val < count <;> simp only [before, ↓reduceIte, prob_mix,
    mul_zero, add_zero]

theorem timingPrefix_pure_of_le (slot : Fin slots) (count : Nat) (before : count ≤ slot.val) :
    (pure slot).timingPrefix count = 0 := by
  apply Finset.sum_eq_zero
  intro other _
  by_cases earlier : other.val < count
  · have different : other ≠ slot := by intro same; subst other; omega
    simp only [earlier, ↓reduceIte, prob_pure_of_ne different]
  · simp only [earlier, ↓reduceIte]

theorem timingPrefix_zero (timing : FinDist (Fin slots)) : timing.timingPrefix 0 = 0 := by
  simp [timingPrefix]

theorem timingPrefix_all (timing : FinDist (Fin slots)) : timing.timingPrefix slots = 1 := by
  simp only [timingPrefix, Fin.is_lt, ↓reduceIte, sum_prob]

theorem timingPrefix_succ (timing : FinDist (Fin slots)) (slot : Fin slots) :
    timing.timingPrefix (slot.val + 1) = timing.timingPrefix slot.val + timing.prob slot := by
  have point (other : Fin slots) :
      (if other.val < slot.val + 1 then timing.prob other else 0) =
        (if other.val < slot.val then timing.prob other else 0) +
          (if other = slot then timing.prob slot else 0) := by
    by_cases same : other = slot
    · subst other
      simp
    · have unequal : other.val ≠ slot.val := fun equal => same (Fin.ext equal)
      by_cases before : other.val < slot.val <;> simp [same, before, show
        (other.val < slot.val + 1) = (other.val < slot.val) from propext (by omega)]
  simp only [timingPrefix, point, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-- Probability that the binary choice has not yet been emitted. -/
def deferredSurvival (probability : ℝ) (timing : FinDist (Fin slots)) (count : Nat) : ℝ :=
  1 - probability * timing.timingPrefix count

theorem deferredSurvival_positive (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (count : Nat) :
    0 < deferredSurvival probability timing count := by
  have atMost := mul_le_mul_of_nonneg_left (timing.timingPrefix_le_one count) nonnegative
  unfold deferredSurvival
  linarith

theorem deferredSurvival_succ (probability : ℝ) (timing : FinDist (Fin slots))
    (slot : Fin slots) :
    deferredSurvival probability timing (slot.val + 1) =
      deferredSurvival probability timing slot.val - probability * timing.prob slot := by
  simp only [deferredSurvival, timingPrefix_succ]
  ring

/-- Conditional probability of an eventual true choice after no earlier
emission. This differs from the immediate hazard at the next opportunity. -/
def deferredRemaining (probability : ℝ) (timing : FinDist (Fin slots)) (count : Nat) : ℝ :=
  probability * (1 - timing.timingPrefix count) / deferredSurvival probability timing count

theorem deferredRemaining_eq (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (count : Nat) :
    deferredRemaining probability timing count =
      1 - (1 - probability) / deferredSurvival probability timing count := by
  have positive := deferredSurvival_positive probability nonnegative small timing count
  unfold deferredRemaining deferredSurvival at *
  field_simp [ne_of_gt positive]
  ring

/-- Waiting changes the eventual binary probability by at most the timing
mass already passed, uniformly even when the original probability tends to one. -/
theorem deferredRemaining_error (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (count : Nat) :
    0 ≤ probability - deferredRemaining probability timing count ∧
      probability - deferredRemaining probability timing count ≤ timing.timingPrefix count := by
  have positive := deferredSurvival_positive probability nonnegative small timing count
  have prefixNonnegative := timing.timingPrefix_nonnegative count
  have prefixBounded := timing.timingPrefix_le_one count
  have exactError : probability - deferredRemaining probability timing count =
      probability * (1 - probability) * timing.timingPrefix count /
        deferredSurvival probability timing count := by
    unfold deferredRemaining deferredSurvival at *
    field_simp [ne_of_gt positive]
    ring
  rw [exactError]
  refine ⟨div_nonneg (mul_nonneg (mul_nonneg nonnegative (by linarith))
    prefixNonnegative) positive.le, (div_le_iff₀ positive).mpr ?_⟩
  have first := sq_nonneg (1 - probability)
  have second := mul_nonneg nonnegative (sub_nonneg.mpr prefixBounded)
  have bound : probability * (1 - probability) ≤
      deferredSurvival probability timing count := by
    unfold deferredSurvival
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right bound prefixNonnegative]

theorem deferredRemaining_nonnegative (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (count : Nat) :
    0 ≤ deferredRemaining probability timing count := by
  exact div_nonneg (mul_nonneg nonnegative (sub_nonneg.mpr (timing.timingPrefix_le_one count)))
    (deferredSurvival_positive probability nonnegative small timing count).le

/-- The conditional value distortion is bounded by passed timing mass times
the difference between the two source continuation values. -/
theorem deferredRemaining_value_error (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (count : Nat)
    (whenTrue whenFalse : ℝ) :
    |(deferredRemaining probability timing count * whenTrue +
        (1 - deferredRemaining probability timing count) * whenFalse) -
      (probability * whenTrue + (1 - probability) * whenFalse)| ≤
        timing.timingPrefix count * |whenTrue - whenFalse| := by
  have error := deferredRemaining_error probability nonnegative small timing count
  have algebra : (deferredRemaining probability timing count * whenTrue +
        (1 - deferredRemaining probability timing count) * whenFalse) -
      (probability * whenTrue + (1 - probability) * whenFalse) =
        -(probability - deferredRemaining probability timing count) *
          (whenTrue - whenFalse) := by ring
  rw [algebra, abs_mul, abs_neg, abs_of_nonneg error.1]
  exact mul_le_mul_of_nonneg_right error.2 (abs_nonneg _)

/-- A local decision to open now or resume later is a lawful binary source
lottery. Its gain differs from that source deviation's gain only by the
prescribed waiting distortion. -/
theorem deferredRemaining_local_comparison (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (count : Nat)
    (immediate : ℝ) (immediateNonnegative : 0 ≤ immediate) (immediateBounded : immediate ≤ 1)
    (whenTrue whenFalse : ℝ) :
    let remaining := deferredRemaining probability timing (count + 1)
    let replacement := immediate + (1 - immediate) * remaining
    0 ≤ replacement ∧ replacement ≤ 1 ∧
      (immediate * whenTrue + (1 - immediate) *
        (remaining * whenTrue + (1 - remaining) * whenFalse)) -
        (deferredRemaining probability timing count * whenTrue +
          (1 - deferredRemaining probability timing count) * whenFalse) ≤
      (replacement * whenTrue + (1 - replacement) * whenFalse) -
        (probability * whenTrue + (1 - probability) * whenFalse) +
          timing.timingPrefix count * |whenTrue - whenFalse| := by
  intro remaining replacement
  have remainingNonnegative : 0 ≤ remaining :=
    deferredRemaining_nonnegative probability nonnegative small timing (count + 1)
  have remainingBounded : remaining ≤ 1 := by
    have lower := (deferredRemaining_error probability nonnegative small timing (count + 1)).1
    change 0 ≤ probability - remaining at lower
    linarith
  refine ⟨add_nonneg immediateNonnegative
    (mul_nonneg (sub_nonneg.mpr immediateBounded) remainingNonnegative), ?_, ?_⟩
  · have upper := mul_le_mul_of_nonneg_left remainingBounded
      (sub_nonneg.mpr immediateBounded)
    dsimp only [replacement]
    linarith
  · have error := deferredRemaining_value_error probability nonnegative small timing count
      whenTrue whenFalse
    have directed := (abs_le.mp error).1
    have algebra : immediate * whenTrue + (1 - immediate) *
        (remaining * whenTrue + (1 - remaining) * whenFalse) =
        replacement * whenTrue + (1 - replacement) * whenFalse := by
      dsimp only [replacement]
      ring
    rw [algebra]
    linarith

/-- Conditional probability of choosing true at an opportunity not yet used.
The value outside the finite opportunity list is irrelevant and is zero. -/
def deferredHazard (probability : ℝ) (timing : FinDist (Fin slots)) (count : Nat) : ℝ :=
  if inside : count < slots then
    probability * timing.prob ⟨count, inside⟩ / deferredSurvival probability timing count
  else 0

theorem deferredHazard_at (probability : ℝ) (timing : FinDist (Fin slots))
    (slot : Fin slots) :
    deferredHazard probability timing slot.val =
      probability * timing.prob slot / deferredSurvival probability timing slot.val := by
  simp only [deferredHazard, slot.isLt, ↓reduceDIte]

/-- Opening with the present hazard and otherwise continuing the same deferred
choice recovers its current conditional probability. -/
theorem deferredRemaining_hazard_recursion (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (slot : Fin slots) :
    deferredHazard probability timing slot.val +
        (1 - deferredHazard probability timing slot.val) *
          deferredRemaining probability timing (slot.val + 1) =
      deferredRemaining probability timing slot.val := by
  have current := deferredSurvival_positive probability nonnegative small timing slot.val
  have next := deferredSurvival_positive probability nonnegative small timing (slot.val + 1)
  rw [deferredSurvival_succ] at next
  rw [deferredHazard_at,
    deferredRemaining_eq probability nonnegative small timing (slot.val + 1),
    deferredRemaining_eq probability nonnegative small timing slot.val,
    deferredSurvival_succ]
  field_simp [ne_of_gt current, ne_of_gt next]
  ring

theorem deferredRemaining_hazard_value (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (slot : Fin slots)
    (whenTrue whenFalse : ℝ) :
    deferredHazard probability timing slot.val * whenTrue +
        (1 - deferredHazard probability timing slot.val) *
          (deferredRemaining probability timing (slot.val + 1) * whenTrue +
            (1 - deferredRemaining probability timing (slot.val + 1)) * whenFalse) =
      deferredRemaining probability timing slot.val * whenTrue +
        (1 - deferredRemaining probability timing slot.val) * whenFalse := by
  rw [← deferredRemaining_hazard_recursion probability nonnegative small timing slot]
  ring

theorem deferredHazard_nonnegative (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (slot : Fin slots) :
    0 ≤ deferredHazard probability timing slot.val := by
  rw [deferredHazard_at]
  exact div_nonneg (mul_nonneg nonnegative (timing.prob_nonneg slot))
    (deferredSurvival_positive probability nonnegative small timing slot.val).le

theorem deferredHazard_lt_one (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (slot : Fin slots) :
    deferredHazard probability timing slot.val < 1 := by
  rw [deferredHazard_at]
  apply (div_lt_one (deferredSurvival_positive probability nonnegative small timing slot.val)).mpr
  have positive := deferredSurvival_positive probability nonnegative small timing (slot.val + 1)
  rw [deferredSurvival_succ] at positive
  linarith

theorem deferredHazard_positive (probability : ℝ) (positive : 0 < probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (full : timing.FullSupport)
    (slot : Fin slots) : 0 < deferredHazard probability timing slot.val := by
  rw [deferredHazard_at]
  exact div_pos (mul_pos positive (prob_pos_iff.mpr (full slot)))
    (deferredSurvival_positive probability positive.le small timing slot.val)

/-- The product of behavioral waiting probabilities is the intended survival
mass. In particular no positive source false mass is lost to deferral. -/
theorem deferredHazard_survival (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (count : Nat)
    (within : count ≤ slots) :
    ∏ opportunity ∈ Finset.range count,
      (1 - deferredHazard probability timing opportunity) =
        deferredSurvival probability timing count := by
  induction count with
  | zero => simp [deferredSurvival, timingPrefix_zero]
  | succ count ih =>
      have inside : count < slots := by omega
      let slot : Fin slots := ⟨count, inside⟩
      rw [Finset.prod_range_succ, ih (by omega)]
      have hazard := deferredHazard_at probability timing slot
      change deferredHazard probability timing count =
        probability * timing.prob slot / deferredSurvival probability timing count at hazard
      rw [hazard]
      have positive := deferredSurvival_positive probability nonnegative small timing count
      have step := deferredSurvival_succ probability timing slot
      change deferredSurvival probability timing (count + 1) =
        deferredSurvival probability timing count - probability * timing.prob slot at step
      rw [step]
      field_simp [ne_of_gt positive]

theorem deferredHazard_first (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (slot : Fin slots) :
    (∏ opportunity ∈ Finset.range slot.val,
      (1 - deferredHazard probability timing opportunity)) *
        deferredHazard probability timing slot.val = probability * timing.prob slot := by
  rw [deferredHazard_survival probability nonnegative small timing slot.val slot.isLt.le,
    deferredHazard_at]
  exact mul_div_cancel₀ _ (ne_of_gt
    (deferredSurvival_positive probability nonnegative small timing slot.val))

theorem deferredHazard_never (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) :
    ∏ opportunity ∈ Finset.range slots,
      (1 - deferredHazard probability timing opportunity) = 1 - probability := by
  rw [deferredHazard_survival probability nonnegative small timing slots le_rfl]
  simp only [deferredSurvival, timingPrefix_all, mul_one]

/-- The complete first-emission/never-emission experiment has the same value
as the original binary choice whenever payoffs depend only on that choice. -/
theorem deferredHazard_value (probability : ℝ) (nonnegative : 0 ≤ probability)
    (small : probability < 1) (timing : FinDist (Fin slots)) (whenTrue whenFalse : ℝ) :
    (∑ slot : Fin slots,
      ((∏ opportunity ∈ Finset.range slot.val,
        (1 - deferredHazard probability timing opportunity)) *
          deferredHazard probability timing slot.val) * whenTrue) +
      (∏ opportunity ∈ Finset.range slots,
        (1 - deferredHazard probability timing opportunity)) * whenFalse =
          probability * whenTrue + (1 - probability) * whenFalse := by
  simp_rw [deferredHazard_first probability nonnegative small timing]
  rw [deferredHazard_never probability nonnegative small timing,
    ← Finset.sum_mul, ← Finset.mul_sum, timing.sum_prob, mul_one]

theorem timingPrefix_tendsto {sequence : ℕ → FinDist (Fin slots)}
    {target : FinDist (Fin slots)} (converges : FinDistConvergesPointwise sequence target)
    (count : Nat) :
    Tendsto (fun n => (sequence n).timingPrefix count) atTop
      (nhds (target.timingPrefix count)) := by
  unfold timingPrefix
  apply tendsto_finsetSum
  intro slot _
  by_cases before : slot.val < count
  · simpa only [before, ↓reduceIte] using converges slot
  · simp only [before, ↓reduceIte]
    exact tendsto_const_nhds

theorem timingPrefix_pure_last (last : Nat) (count : Nat) (before : count ≤ last) :
    (pure (Fin.last last)).timingPrefix count = 0 := by
  apply Finset.sum_eq_zero
  intro slot _
  by_cases earlier : slot.val < count
  · have different : slot ≠ Fin.last last := by
      intro same
      subst slot
      simp only [Fin.val_last] at earlier
      omega
    simp only [earlier, ↓reduceIte, prob_pure_of_ne different]
  · simp only [earlier, ↓reduceIte]

/-- One timing sequence removes the conditional distortion uniformly over
arbitrary source probabilities, with no lower bound on source trembles. -/
theorem deferredRemaining_error_tendsto {last : Nat} (probability : ℕ → ℝ)
    (nonnegative : ∀ n, 0 ≤ probability n) (small : ∀ n, probability n < 1)
    {timing : ℕ → FinDist (Fin (last + 1))}
    (timingConverges : FinDistConvergesPointwise timing (pure (Fin.last last)))
    (count : Nat) (before : count ≤ last) :
    Tendsto (fun n => probability n - deferredRemaining (probability n) (timing n) count)
      atTop (nhds 0) := by
  have vanishes := timingPrefix_tendsto timingConverges count
  rw [timingPrefix_pure_last last count before] at vanishes
  exact squeeze_zero
    (fun n => (deferredRemaining_error _ (nonnegative n) (small n) _ _).1)
    (fun n => (deferredRemaining_error _ (nonnegative n) (small n) _ _).2) vanishes

/-- Concentrating conditional timing on the final opportunity yields zero
earlier hazards and the original choice probability at the last opportunity.
The conclusion also holds when the limiting choice probability is one: the
relevant survival denominators converge to one, rather than zero. -/
theorem deferredHazard_tendsto_last {last : Nat} {probability : ℕ → ℝ}
    {limit : ℝ} (probabilityConverges : Tendsto probability atTop (nhds limit))
    {timing : ℕ → FinDist (Fin (last + 1))}
    (timingConverges : FinDistConvergesPointwise timing (pure (Fin.last last)))
    (slot : Fin (last + 1)) :
    Tendsto (fun n => deferredHazard (probability n) (timing n) slot.val) atTop
      (nhds (if slot = Fin.last last then limit else 0)) := by
  have prefixConverges := timingPrefix_tendsto timingConverges slot.val
  rw [timingPrefix_pure_last last slot.val (by omega)] at prefixConverges
  have one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have denominator := one.sub (probabilityConverges.mul prefixConverges)
  have numerator := probabilityConverges.mul (timingConverges slot)
  have quotient := numerator.div denominator (by norm_num : (1 : ℝ) - limit * 0 ≠ 0)
  simpa only [deferredHazard_at, deferredSurvival, prob_pure_eq_ite,
    mul_ite, mul_zero, mul_one, sub_zero, div_one, Pi.div_def] using quotient

/-- A fully supported timing perturbation around the final opportunity. -/
def finalTiming (last : Nat) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bounded : weight ≤ 1) : FinDist (Fin (last + 1)) :=
  mix weight nonnegative bounded uniformOfFintype (pure (Fin.last last))

theorem finalTiming_fullSupport (last : Nat) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bounded : weight ≤ 1) (positive : 0 < weight) :
    (finalTiming last weight nonnegative bounded).FullSupport := by
  intro slot
  exact mem_support_mix_left weight nonnegative bounded positive
    (mem_support_uniformOfFintype slot)

theorem finalTiming_tendsto (last : Nat) {weight : ℕ → ℝ}
    (nonnegative : ∀ n, 0 ≤ weight n) (bounded : ∀ n, weight n ≤ 1)
    (converges : Tendsto weight atTop (nhds 0)) :
    FinDistConvergesPointwise
      (fun n => finalTiming last (weight n) (nonnegative n) (bounded n))
      (pure (Fin.last last)) := by
  intro slot
  have first := converges.mul_const ((uniformOfFintype : FinDist (Fin (last + 1))).prob slot)
  have one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have second := (one.sub converges).mul_const ((pure (Fin.last last)).prob slot)
  simpa only [finalTiming, prob_mix, zero_mul, sub_zero, one_mul, zero_add] using
    first.add second

end GameTheory.Math.Probability.FinDist
