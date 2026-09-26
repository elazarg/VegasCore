/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.KernelDomination
import GameTheory.Math.Probability.Convergence

/-! # Conditional laws under near-unit probability domination

The target law may put additional mass on any history. A multiplicative lower
bound on the entire embedded source law controls the remaining mass, hence the
Bayes posterior even when conditioning on an event that becomes arbitrarily rare.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

namespace FinDist

/-- Conditioning commutes with an injective encoding when the two events
correspond on encoded values. Extra target values need not have source names. -/
theorem map_condOn_embedding {Source Target : Type*} (law : FinDist Source)
    (embed : Source ↪ Target) (sourceEvent : Set Source) (targetEvent : Set Target)
    (corresponds : ∀ state, embed state ∈ targetEvent ↔ state ∈ sourceEvent)
    (sourceMeet : ∃ state ∈ sourceEvent, state ∈ law.support)
    (targetMeet : ∃ state ∈ targetEvent, state ∈ (law.map embed).support) :
    (law.condOn sourceEvent sourceMeet).map embed =
      (law.map embed).condOn targetEvent targetMeet := by
  classical
  have preimage : embed ⁻¹' targetEvent = sourceEvent := Set.ext corresponds
  have mass : (law.map embed).probOf targetEvent = law.probOf sourceEvent := by
    rw [probOf_map, preimage]
  apply ext_of_prob
  intro value
  by_cases encoded : value ∈ Set.range embed
  · obtain ⟨original, rfl⟩ := encoded
    rw [prob_map_of_injective embed embed.injective, prob_condOn, prob_condOn,
      prob_map_of_injective embed embed.injective, mass, corresponds]
  · have unsupported (distribution : FinDist Source) : (distribution.map embed).prob value = 0 := by
      apply prob_eq_zero_iff.mpr
      rw [support_map]
      rintro ⟨original, _, same⟩
      exact encoded ⟨original, same⟩
    rw [unsupported, prob_condOn, unsupported]
    split_ifs <;> simp

variable {State : Type*} [Finite State]

theorem probOf_domination (source target : FinDist State) (factor : ℝ)
    (lower : ∀ state, factor * source.prob state ≤ target.prob state) (event : Set State) :
    factor * source.probOf event ≤ target.probOf event := by
  classical
  rw [← expect_indicator_eq_probOf, ← expect_indicator_eq_probOf]
  exact mul_expect_le_of_prob_le source target factor lower _ (fun state => by
    split_ifs <;> norm_num)

omit [Finite State] in
private theorem probOf_add_compl (law : FinDist State) (event : Set State) :
    law.probOf event + law.probOf eventᶜ = 1 := by
  classical
  rw [← expect_indicator_eq_probOf, ← expect_indicator_eq_probOf, ← expect_add]
  calc
    _ = law.expect (fun _ => (1 : ℝ)) := by
      apply expect_congr
      intro state _
      by_cases member : state ∈ event <;> simp [member]
    _ = 1 := expect_const _ _

/-- All mass in excess of the dominated source component is at most its
missing normalization mass, including after restricting to an event. -/
theorem probOf_domination_excess (source target : FinDist State) (factor : ℝ)
    (lower : ∀ state, factor * source.prob state ≤ target.prob state) (event : Set State) :
    target.probOf event - factor * source.probOf event ≤ 1 - factor := by
  have complement := probOf_domination source target factor lower eventᶜ
  have sourceTotal := probOf_add_compl source event
  have targetTotal := probOf_add_compl target event
  have scaled := congrArg (fun value => factor * value) sourceTotal
  rw [mul_add, mul_one] at scaled
  linarith

private theorem ratio_domination_bound (point mass changed total factor : ℝ)
    (massPositive : 0 < mass) (totalPositive : 0 < total)
    (pointNonnegative : 0 ≤ point) (pointWithin : point ≤ mass)
    (factorPositive : 0 < factor) (factorAtMostOne : factor ≤ 1)
    (pointLower : factor * point ≤ changed)
    (pointExcess : changed - factor * point ≤ 1 - factor)
    (massLower : factor * mass ≤ total)
    (massExcess : total - factor * mass ≤ 1 - factor) :
    |changed / total - point / mass| ≤ (1 - factor) / (factor * mass) := by
  have fractionNonnegative : 0 ≤ point / mass := div_nonneg pointNonnegative massPositive.le
  have fractionAtMostOne : point / mass ≤ 1 := (div_le_one massPositive).mpr pointWithin
  have excessNonnegative : 0 ≤ total - factor * mass := sub_nonneg.mpr massLower
  have missingNonnegative : 0 ≤ 1 - factor := sub_nonneg.mpr factorAtMostOne
  have scaledNonnegative := mul_nonneg fractionNonnegative excessNonnegative
  have scaledUpper : (point / mass) * (total - factor * mass) ≤ 1 - factor :=
    (mul_le_mul_of_nonneg_left massExcess fractionNonnegative).trans
      (mul_le_of_le_one_left missingNonnegative fractionAtMostOne)
  have numerator : |(changed - factor * point) -
      (point / mass) * (total - factor * mass)| ≤ 1 - factor := by
    apply abs_le.mpr
    constructor <;> linarith
  have difference : changed / total - point / mass =
      ((changed - factor * point) - (point / mass) * (total - factor * mass)) / total := by
    field_simp
    ring
  rw [difference, abs_div, abs_of_pos totalPositive]
  exact (div_le_div_of_nonneg_right numerator totalPositive.le).trans
    (div_le_div_of_nonneg_left missingNonnegative (mul_pos factorPositive massPositive)
      massLower)

/-- Domination by a near-unit source component bounds each posterior error by
the missing mass divided by the retained source event mass. -/
theorem conditional_domination_bound (source target : FinDist State) (event : Set State)
    (sourceMeet : ∃ state ∈ event, state ∈ source.support)
    (targetMeet : ∃ state ∈ event, state ∈ target.support)
    (factor : ℝ) (positive : 0 < factor) (atMostOne : factor ≤ 1)
    (lower : ∀ state, factor * source.prob state ≤ target.prob state) (state : State) :
    |(target.condOn event targetMeet).prob state -
      (source.condOn event sourceMeet).prob state| ≤
        (1 - factor) / (factor * source.probOf event) := by
  classical
  have sourcePositive := probOf_pos sourceMeet
  have targetPositive := probOf_pos targetMeet
  rw [prob_condOn, prob_condOn]
  by_cases member : state ∈ event
  · rw [ite_eq_left member, ite_eq_left member]
    have pointWithin : source.prob state ≤ source.probOf event := by
      have normalized := (source.condOn event sourceMeet).prob_le_one state
      rw [prob_condOn, ite_eq_left member] at normalized
      exact (div_le_one sourcePositive).mp normalized
    have pointExcess : target.prob state - factor * source.prob state ≤ 1 - factor := by
      simpa only [probOf_singleton] using
        probOf_domination_excess source target factor lower {state}
    exact ratio_domination_bound _ _ _ _ _ sourcePositive targetPositive
      (source.prob_nonneg state) pointWithin positive atMostOne (lower state) pointExcess
      (probOf_domination source target factor lower event)
      (probOf_domination_excess source target factor lower event)
  · rw [ite_eq_right member, ite_eq_right member, sub_self, abs_zero]
    exact div_nonneg (sub_nonneg.mpr atMostOne) (mul_pos positive sourcePositive).le

end FinDist

/-- A vanishing relative loss transports conditioned laws without any lower
bound on the limiting probability of the conditioning event. -/
theorem conditional_domination_converges {State : Type*} [Finite State]
    (source target : ℕ → FinDist State) (event : Set State)
    (sourceMeet : ∀ n, ∃ state ∈ event, state ∈ (source n).support)
    (targetMeet : ∀ n, ∃ state ∈ event, state ∈ (target n).support)
    (factor : ℕ → ℝ) (positive : ∀ n, 0 < factor n) (atMostOne : ∀ n, factor n ≤ 1)
    (lower : ∀ n state, factor n * (source n).prob state ≤ (target n).prob state)
    (negligible : Tendsto (fun n =>
      (1 - factor n) / (factor n * (source n).probOf event)) atTop (nhds 0))
    (limit : FinDist State)
    (converges : FinDistConvergesPointwise
      (fun n => (source n).condOn event (sourceMeet n)) limit) :
    FinDistConvergesPointwise (fun n => (target n).condOn event (targetMeet n)) limit := by
  intro state
  apply (converges state).congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ negligible
  intro n
  simpa only [Real.dist_eq, abs_sub_comm] using
    FinDist.conditional_domination_bound (source n) (target n) event
      (sourceMeet n) (targetMeet n) (factor n) (positive n) (atMostOne n) (lower n) state

end GameTheory.Math.Probability
