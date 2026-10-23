/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Transporting a marginal through an approximate product factorization

Let `π : Ω → O × E` project finitely many *regular* outcomes onto pairs of a
retained coordinate `o` and an excluded coordinate `e`. Suppose a source law
on `O × E` is a product `q (o, e) = A o * B e` on the whole of `O × E`, zeros
allowed, and a weight `p` on regular outcomes factors through it up to
relative errors: `p h` is `q (π h) * N h` up to a factor `1 ± ε`, and the
operational weights `N` of each fiber `π⁻¹ (o, e)` sum to `K e` up to a factor
`1 ± δ`, where `K` does not depend on `o`. Then the excluded coordinate sums
out of both laws over the same set `E`, leaving `A o` times a constant, so the
normalized `O`-marginal of `p` is close to that of `q`; neither the posterior
of the excluded coordinate nor any single fiber is compared. Irregular
outcomes of total weight at most `η` times the regular weight move the
normalized marginal by at most `2 * η` more.

Distances are measured by the `ℓ¹` distance `∑ o, |P o - Q o|` between the
normalized marginals, twice the total variation distance. The statements work
with real weights on finite types and `Finset` sums rather than `PMF`s: the
weights are unnormalized, the bounds are multiplicative, and the conclusion
is about explicit ratios, all of which are direct real-arithmetic facts.

The asymptotic form takes the errors `ε n`, `δ n`, `η n` to zero along a
sequence of stages and concludes that the `ℓ¹` distance tends to zero, so the
two marginals have the same limits along every subsequence.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Finset Filter Topology

variable {α Ω Ψ O E : Type*}

/-- Normalizing two weight vectors whose total pointwise difference is at
most `γ` times the total of the nonnegative second one moves them at most
`2 * γ / l` apart in `ℓ¹`, when the first total is at least `l > 0` times the
second. -/
theorem sum_abs_div_sum_sub_div_sum_le [Fintype α] {u v : α → ℝ} {γ l : ℝ}
    (v_nonneg : ∀ a, 0 ≤ v a) (v_pos : 0 < ∑ a, v a)
    (close : ∑ a, |u a - v a| ≤ γ * ∑ a, v a)
    (l_pos : 0 < l) (lower : l * ∑ a, v a ≤ ∑ a, u a) :
    ∑ a, |u a / ∑ b, u b - v a / ∑ b, v b| ≤ 2 * γ / l := by
  set U := ∑ b, u b
  set V := ∑ b, v b
  have U_pos : 0 < U := lt_of_lt_of_le (mul_pos l_pos v_pos) lower
  have γ_nonneg : 0 ≤ γ :=
    nonneg_of_mul_nonneg_left ((sum_nonneg fun a _ => abs_nonneg _).trans close) v_pos
  have pointwise : ∀ a, |u a / U - v a / V| ≤
      |u a - v a| / U + v a * |V - U| / (U * V) := fun a => by
    have split : u a / U - v a / V = (u a - v a) / U + v a * (V - U) / (U * V) := by
      field_simp
      ring
    rw [split]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_div, abs_mul, abs_of_pos U_pos, abs_of_nonneg (v_nonneg a),
      abs_of_pos (mul_pos U_pos v_pos)]
  have total_gap : |V - U| ≤ γ * V := by
    have : V - U = ∑ a, (v a - u a) := by simp only [V, U, sum_sub_distrib]
    rw [this]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simpa only [abs_sub_comm] using close
  calc ∑ a, |u a / U - v a / V|
      ≤ ∑ a, (|u a - v a| / U + v a * |V - U| / (U * V)) := sum_le_sum fun a _ => pointwise a
    _ = (∑ a, |u a - v a|) / U + |V - U| / U := by
        rw [sum_add_distrib, ← sum_div, ← sum_div, ← sum_mul]
        change _ + V * |V - U| / (U * V) = _
        rw [mul_comm U V, mul_div_mul_left _ _ v_pos.ne']
    _ ≤ γ * V / U + γ * V / U := by gcongr
    _ = 2 * γ * V / U := by ring
    _ ≤ 2 * γ / l := by
        rw [div_le_div_iff₀ U_pos l_pos]
        nlinarith

/-- Mass of the regular outcomes whose retained coordinate is `o`, split over
the excluded coordinate. -/
private theorem sum_fst_eq_sum_fiber [Fintype Ω] [Fintype E] [DecidableEq O] [DecidableEq E]
    (π : Ω → O × E) (w : Ω → ℝ) (o : O) :
    ∑ h with (π h).1 = o, w h = ∑ e, ∑ h with π h = (o, e), w h := by
  rw [← sum_fiberwise_of_maps_to (g := fun h => (π h).2) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun e _ => ?_
  rw [filter_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext h
  simp only [mem_filter, mem_univ, true_and, Prod.ext_iff]

/-- **Transport of a marginal through an approximate product factorization.**
If the source weights are a product `q (o, e) = A o * B e` on all of `O × E`,
each regular weight `p h` is `q (π h) * N h` up to relative error `ε`, and
each fiber of the operational weights `N` sums to `K e` up to relative error
`δ`, with `K` independent of `o`, then the normalized `O`-marginals of `p`
and `q` are within `2 * (ε + δ + ε * δ) / ((1 - ε) * (1 - δ))` in `ℓ¹`. -/
theorem sum_abs_marginal_sub_marginal_le_of_product [Fintype Ω] [Fintype O] [Fintype E]
    [DecidableEq O] [DecidableEq E] (π : Ω → O × E) (p N : Ω → ℝ) (q : O × E → ℝ)
    (A : O → ℝ) (B K : E → ℝ) {ε δ : ℝ}
    (A_nonneg : ∀ o, 0 ≤ A o) (B_nonneg : ∀ e, 0 ≤ B e)
    (K_nonneg : ∀ e, 0 ≤ K e)
    (product : ∀ o e, q (o, e) = A o * B e)
    (factor : ∀ h, |p h - q (π h) * N h| ≤ ε * (q (π h) * N h))
    (fiber : ∀ o e, |(∑ h with π h = (o, e), N h) - K e| ≤ δ * K e)
    (ε_nonneg : 0 ≤ ε) (ε_lt_one : ε < 1) (δ_nonneg : 0 ≤ δ) (δ_lt_one : δ < 1)
    (possible : 0 < ∑ h, p h) :
    ∑ o, |(∑ h with (π h).1 = o, p h) / (∑ h, p h) - (∑ e, q (o, e)) / ∑ x, q x| ≤
      2 * (ε + δ + ε * δ) / ((1 - ε) * (1 - δ)) := by
  set γ := ε + δ + ε * δ
  set C := ∑ e, B e * K e
  set m : O → ℝ := fun o => ∑ h with (π h).1 = o, p h
  set v : O → ℝ := fun o => A o * C
  have C_nonneg : 0 ≤ C := sum_nonneg fun e _ => mul_nonneg (B_nonneg e) (K_nonneg e)
  have v_nonneg : ∀ o, 0 ≤ v o := fun o => mul_nonneg (A_nonneg o) C_nonneg
  -- Each fiber `(o, e)` carries regular mass `A o * B e * K e` up to the two errors.
  have fiber_bounds : ∀ o e,
      |(∑ h with π h = (o, e), p h) - A o * B e * K e| ≤ γ * (A o * B e * K e) ∧
        (1 - ε) * (1 - δ) * (A o * B e * K e) ≤ ∑ h with π h = (o, e), p h := by
    intro o e
    set S := ∑ h with π h = (o, e), N h
    have AB_nonneg : 0 ≤ A o * B e := mul_nonneg (A_nonneg o) (B_nonneg e)
    have on_fiber : ∀ h ∈ ({h | π h = (o, e)} : Finset Ω),
        |p h - A o * B e * N h| ≤ ε * (A o * B e * N h) := fun h mem => by
      have := factor h
      rwa [(mem_filter.mp mem).2, product] at this
    have deviation : |(∑ h with π h = (o, e), p h) - A o * B e * S| ≤ ε * (A o * B e * S) := by
      rw [show A o * B e * S = ∑ h with π h = (o, e), A o * B e * N h by rw [mul_sum],
        ← sum_sub_distrib, mul_sum]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum on_fiber)
    have S_close := abs_le.mp (fiber o e)
    have K_part : |A o * B e * S - A o * B e * K e| ≤ δ * (A o * B e * K e) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg AB_nonneg]
      nlinarith [fiber o e]
    have S_le : A o * B e * S ≤ (1 + δ) * (A o * B e * K e) := by nlinarith
    have S_ge : (1 - δ) * (A o * B e * K e) ≤ A o * B e * S := by nlinarith
    have dev := abs_le.mp deviation
    have Kp := abs_le.mp K_part
    have ABK_nonneg : 0 ≤ A o * B e * K e := mul_nonneg AB_nonneg (K_nonneg e)
    constructor
    · refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith
    · nlinarith
  have m_split : ∀ o, m o = ∑ e, ∑ h with π h = (o, e), p h := fun o =>
    sum_fst_eq_sum_fiber π p o
  have v_split : ∀ o, v o = ∑ e, A o * B e * K e := fun o => by
    simp only [v, C, mul_sum, mul_assoc]
  have close_pointwise : ∀ o, |m o - v o| ≤ γ * v o := fun o => by
    rw [m_split, v_split, ← sum_sub_distrib, mul_sum]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e _ => (fiber_bounds o e).1)
  have lower_pointwise : ∀ o, (1 - ε) * (1 - δ) * v o ≤ m o := fun o => by
    rw [m_split, v_split, mul_sum]
    exact sum_le_sum fun e _ => (fiber_bounds o e).2
  have m_total : ∑ o, m o = ∑ h, p h := sum_fiberwise univ (fun h => (π h).1) p
  have γ_nonneg : 0 ≤ γ := by positivity
  -- The comparison weight `A o * C` has positive total since the regular mass does.
  have v_pos : 0 < ∑ o, v o := by
    have upper : ∑ o, m o ≤ (1 + γ) * ∑ o, v o := by
      rw [mul_sum]
      exact sum_le_sum fun o _ => by linarith [(abs_le.mp (close_pointwise o)).2]
    rw [m_total] at upper
    by_contra not_pos
    have : ∑ o, v o = 0 := le_antisymm (not_lt.mp not_pos) (sum_nonneg fun o _ => v_nonneg o)
    rw [this, mul_zero] at upper
    linarith
  have v_total : ∑ o, v o = (∑ o, A o) * C := by simp only [v, sum_mul]
  have A_total_pos : 0 < ∑ o, A o := by
    refine lt_of_le_of_ne (sum_nonneg fun o _ => A_nonneg o) fun zero => ?_
    rw [v_total, ← zero, zero_mul] at v_pos
    exact lt_irrefl _ v_pos
  have C_pos : 0 < C := by
    refine lt_of_le_of_ne C_nonneg fun zero => ?_
    rw [v_total, ← zero, mul_zero] at v_pos
    exact lt_irrefl _ v_pos
  have B_total_pos : 0 < ∑ e, B e := by
    refine lt_of_le_of_ne (sum_nonneg fun e _ => B_nonneg e) fun zero => ?_
    have all_zero := (sum_eq_zero_iff_of_nonneg fun e _ => B_nonneg e).mp zero.symm
    have : C = 0 := sum_eq_zero fun e mem => by rw [all_zero e mem, zero_mul]
    exact C_pos.ne' this
  have source_eq : ∀ o, (∑ e, q (o, e)) / ∑ x, q x = v o / ∑ o', v o' := fun o => by
    have row : ∑ e, q (o, e) = A o * ∑ e, B e := by simp only [product, mul_sum]
    have total : ∑ x, q x = (∑ o, A o) * ∑ e, B e := by
      rw [Fintype.sum_prod_type, sum_mul]
      exact sum_congr rfl fun o _ => by simp only [product, mul_sum]
    rw [row, total, v_total]
    simp only [v]
    field_simp
  have l_pos : 0 < (1 - ε) * (1 - δ) := mul_pos (by linarith) (by linarith)
  have main := sum_abs_div_sum_sub_div_sum_le v_nonneg v_pos
    (by rw [mul_sum]; exact sum_le_sum fun o _ => close_pointwise o)
    l_pos (by rw [mul_sum]; exact sum_le_sum fun o _ => lower_pointwise o)
  refine (le_of_eq (sum_congr rfl fun o _ => ?_)).trans main
  rw [m_total, source_eq o]

/-- Adding nonnegative mass of total at most `η` times the total of a
nonnegative weight moves its normalization at most `2 * η` in `ℓ¹`. This
holds however the added mass is spread over the coordinates. -/
theorem sum_abs_div_sum_add_sub_div_sum_le [Fintype α] {m s : α → ℝ} {η : ℝ}
    (m_nonneg : ∀ a, 0 ≤ m a) (s_nonneg : ∀ a, 0 ≤ s a) (m_pos : 0 < ∑ a, m a)
    (small : ∑ a, s a ≤ η * ∑ a, m a) :
    ∑ a, |(m a + s a) / ∑ b, (m b + s b) - m a / ∑ b, m b| ≤ 2 * η := by
  have bound := sum_abs_div_sum_sub_div_sum_le (u := fun a => m a + s a) (γ := η)
    m_nonneg m_pos ?_ one_pos ?_
  · rwa [div_one] at bound
  · simpa only [add_sub_cancel_left, abs_of_nonneg (s_nonneg _)] using small
  · rw [one_mul, sum_add_distrib]
    linarith [sum_nonneg fun a (_ : a ∈ univ) => s_nonneg a]

/-- Stage data for transporting a marginal through an approximate product
factorization. Regular outcomes `Ω` project by `π` onto pairs of a retained
coordinate in `O` and an excluded coordinate in `E`; irregular outcomes `Ψ`
carry only a retained coordinate `ω`. The regular weight factors through the
product source law `source (o, e) = left o * right e` and the operational
weight up to relative error `factorError`; each fiber of the operational
weight sums to `fiberMass e`, independent of `o`, up to relative error
`fiberError`; and the irregular weight is at most `remainderRatio` times the
regular weight. -/
structure NearProductWeights [Fintype Ω] [Fintype Ψ] [DecidableEq O] [DecidableEq E]
    (π : Ω → O × E) (ω : Ψ → O) where
  /-- Weight of each regular outcome. -/
  regular : Ω → ℝ
  /-- Weight of each irregular outcome. -/
  remainder : Ψ → ℝ
  /-- The source law on retained and excluded coordinates. -/
  source : O × E → ℝ
  /-- Retained factor of the source law. -/
  left : O → ℝ
  /-- Excluded factor of the source law. -/
  right : E → ℝ
  /-- Operational weight of each regular outcome beyond its source weight. -/
  operational : Ω → ℝ
  /-- Common operational mass of the fibers with excluded coordinate `e`. -/
  fiberMass : E → ℝ
  /-- Relative error of the factorization of the regular weight. -/
  factorError : ℝ
  /-- Relative error of the operational fiber masses. -/
  fiberError : ℝ
  /-- Irregular mass relative to the regular mass. -/
  remainderRatio : ℝ
  left_nonneg : ∀ o, 0 ≤ left o
  right_nonneg : ∀ e, 0 ≤ right e
  operational_nonneg : ∀ h, 0 ≤ operational h
  fiberMass_nonneg : ∀ e, 0 ≤ fiberMass e
  remainder_nonneg : ∀ g, 0 ≤ remainder g
  source_eq_mul : ∀ o e, source (o, e) = left o * right e
  regular_close : ∀ h, |regular h - source (π h) * operational h| ≤
    factorError * (source (π h) * operational h)
  fiber_close : ∀ o e, |(∑ h with π h = (o, e), operational h) - fiberMass e| ≤
    fiberError * fiberMass e
  factorError_nonneg : 0 ≤ factorError
  factorError_lt_one : factorError < 1
  fiberError_nonneg : 0 ≤ fiberError
  fiberError_lt_one : fiberError < 1
  remainder_le : ∑ g, remainder g ≤ remainderRatio * ∑ h, regular h
  regular_pos : 0 < ∑ h, regular h

namespace NearProductWeights

variable [Fintype Ω] [Fintype Ψ] [DecidableEq O] [DecidableEq E]
  {π : Ω → O × E} {ω : Ψ → O}

/-- The `ℓ¹` bound between the native and source retained-coordinate laws, in
terms of the three relative errors. -/
def errorBound (w : NearProductWeights π ω) : ℝ :=
  2 * (w.factorError + w.fiberError + w.factorError * w.fiberError) /
      ((1 - w.factorError) * (1 - w.fiberError)) + 2 * w.remainderRatio

/-- Regular weights are nonnegative, since they are within a relative error
below one of nonnegative products. -/
theorem regular_nonneg (w : NearProductWeights π ω) (h : Ω) : 0 ≤ w.regular h := by
  have weight_nonneg : 0 ≤ w.source (π h) * w.operational h := by
    rw [w.source_eq_mul]
    exact mul_nonneg (mul_nonneg (w.left_nonneg _) (w.right_nonneg _)) (w.operational_nonneg h)
  have close := (abs_le.mp (w.regular_close h)).1
  nlinarith [w.factorError_lt_one]

variable [Fintype O] [Fintype E]

/-- The normalized law of the retained coordinate under all regular and
irregular outcomes. -/
def nativeLaw (w : NearProductWeights π ω) (o : O) : ℝ :=
  ((∑ h with (π h).1 = o, w.regular h) + ∑ g with ω g = o, w.remainder g) /
    ((∑ h, w.regular h) + ∑ g, w.remainder g)

/-- The normalized law of the retained coordinate under the source law. -/
def sourceLaw (w : NearProductWeights π ω) (o : O) : ℝ :=
  (∑ e, w.source (o, e)) / ∑ x, w.source x

/-- The normalized retained-coordinate laws of the native and source weights
are within `errorBound` in `ℓ¹`. -/
theorem sum_abs_nativeLaw_sub_sourceLaw_le (w : NearProductWeights π ω) :
    ∑ o, |w.nativeLaw o - w.sourceLaw o| ≤ w.errorBound := by
  set m : O → ℝ := fun o => ∑ h with (π h).1 = o, w.regular h
  set s : O → ℝ := fun o => ∑ g with ω g = o, w.remainder g
  have m_total : ∑ o, m o = ∑ h, w.regular h := sum_fiberwise univ (fun h => (π h).1) _
  have s_total : ∑ o, s o = ∑ g, w.remainder g := sum_fiberwise univ ω _
  have native_eq : ∀ o, w.nativeLaw o = (m o + s o) / ∑ o', (m o' + s o') := fun o => by
    rw [sum_add_distrib, m_total, s_total]
    rfl
  have contamination := sum_abs_div_sum_add_sub_div_sum_le
    (fun o => sum_nonneg fun h _ => w.regular_nonneg h)
    (fun o => sum_nonneg fun g _ => w.remainder_nonneg g)
    (m_total ▸ w.regular_pos) (show ∑ o, s o ≤ w.remainderRatio * ∑ o, m o by
      rw [m_total, s_total]
      exact w.remainder_le)
  have regular := sum_abs_marginal_sub_marginal_le_of_product π w.regular w.operational
    w.source w.left w.right w.fiberMass w.left_nonneg w.right_nonneg w.fiberMass_nonneg
    w.source_eq_mul w.regular_close w.fiber_close w.factorError_nonneg w.factorError_lt_one
    w.fiberError_nonneg w.fiberError_lt_one w.regular_pos
  rw [← m_total] at regular
  calc ∑ o, |w.nativeLaw o - w.sourceLaw o|
      ≤ ∑ o, (|(m o + s o) / ∑ o', (m o' + s o') - m o / ∑ o', m o'| +
          |m o / ∑ o', m o' - w.sourceLaw o|) := sum_le_sum fun o _ => by
        rw [native_eq]
        exact abs_sub_le _ _ _
    _ ≤ 2 * w.remainderRatio +
          2 * (w.factorError + w.fiberError + w.factorError * w.fiberError) /
            ((1 - w.factorError) * (1 - w.fiberError)) := by
        rw [sum_add_distrib]
        exact add_le_add contamination regular
    _ = w.errorBound := add_comm _ _

end NearProductWeights

end GameTheory.Math.Probability
