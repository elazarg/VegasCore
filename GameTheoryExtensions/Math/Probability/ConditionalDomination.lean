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

/-- Conditioning commutes with an injective encoding when the two events
correspond on encoded values. Extra target values need not have source names. -/
theorem map_filter_embedding {Source Target : Type*} (law : PMF Source)
    (embed : Source ↪ Target) (sourceEvent : Set Source) (targetEvent : Set Target)
    (corresponds : ∀ state, embed state ∈ targetEvent ↔ state ∈ sourceEvent)
    (sourceMeet : ∃ state ∈ sourceEvent, state ∈ law.support)
    (targetMeet : ∃ state ∈ targetEvent, state ∈ (law.map embed).support) :
    (law.filter sourceEvent sourceMeet).map embed =
      (law.map embed).filter targetEvent targetMeet := by
  classical
  have preimage : embed ⁻¹' targetEvent = sourceEvent := Set.ext corresponds
  have mass : (law.map embed).toOuterMeasure targetEvent = law.toOuterMeasure sourceEvent := by
    rw [PMF.toOuterMeasure_map_apply, preimage]
  ext value
  by_cases encoded : value ∈ Set.range embed
  · obtain ⟨original, rfl⟩ := encoded
    rw [pmf_map_apply_of_injective _ embed.injective, PMF.filter_apply, PMF.filter_apply,
      ← PMF.toOuterMeasure_apply, ← PMF.toOuterMeasure_apply, mass]
    by_cases member : original ∈ sourceEvent
    · rw [Set.indicator_of_mem member, Set.indicator_of_mem ((corresponds original).mpr member),
        pmf_map_apply_of_injective _ embed.injective]
    · rw [Set.indicator_of_notMem member,
        Set.indicator_of_notMem fun inside => member ((corresponds original).mp inside)]
  · have unsupported (distribution : PMF Source) : (distribution.map embed) value = 0 := by
      apply (PMF.apply_eq_zero_iff _ _).mpr
      rw [PMF.support_map]
      rintro ⟨original, _, same⟩
      exact encoded ⟨original, same⟩
    rw [unsupported, PMF.filter_apply, Set.indicator_apply]
    split_ifs <;> simp [unsupported]

variable {State : Type*} [Finite State]

theorem probOf_domination (source target : PMF State) (factor : ℝ)
    (lower : ∀ state, factor * (source state).toReal ≤ (target state).toReal) (event : Set State) :
    factor * (source.toOuterMeasure event).toReal ≤ (target.toOuterMeasure event).toReal := by
  classical
  rw [← expect_indicator, ← expect_indicator]
  exact PMF.mul_expect_le_of_prob_le source target factor lower _ (fun state => by
    split_ifs <;> norm_num)

omit [Finite State] in
private theorem probOf_add_compl (law : PMF State) (event : Set State) :
    (law.toOuterMeasure event).toReal + (law.toOuterMeasure eventᶜ).toReal = 1 := by
  classical
  rw [← expect_indicator, ← expect_indicator,
    ← expect_add (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split_ifs <;> norm_num)
      (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split_ifs <;> norm_num)]
  calc
    _ = expect law (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro state _
      by_cases member : state ∈ event <;> simp [member]
    _ = 1 := expect_constant _ _

/-- All mass in excess of the dominated source component is at most its
missing normalization mass, including after restricting to an event. -/
theorem probOf_domination_excess (source target : PMF State) (factor : ℝ)
    (lower : ∀ state, factor * (source state).toReal ≤ (target state).toReal) (event : Set State) :
    (target.toOuterMeasure event).toReal - factor * (source.toOuterMeasure event).toReal ≤ 1 -
        factor := by
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
theorem conditional_domination_bound (source target : PMF State) (event : Set State)
    (sourceMeet : ∃ state ∈ event, state ∈ source.support)
    (targetMeet : ∃ state ∈ event, state ∈ target.support)
    (factor : ℝ) (positive : 0 < factor) (atMostOne : factor ≤ 1)
    (lower : ∀ state, factor * (source state).toReal ≤ (target state).toReal) (state : State) :
    |((target.filter event targetMeet) state).toReal -
      ((source.filter event sourceMeet) state).toReal| ≤
        (1 - factor) / (factor * (source.toOuterMeasure event).toReal) := by
  classical
  have sourcePositive := toOuterMeasure_toReal_pos source sourceMeet
  have targetPositive := toOuterMeasure_toReal_pos target targetMeet
  rw [toReal_filter_apply, toReal_filter_apply]
  by_cases member : state ∈ event
  · rw [ite_eq_left member, ite_eq_left member]
    have pointWithin : (source state).toReal ≤ (source.toOuterMeasure event).toReal := by
      have normalized := pmf_toReal_apply_le_one (source.filter event sourceMeet) state
      rw [toReal_filter_apply, ite_eq_left member] at normalized
      exact (div_le_one sourcePositive).mp normalized
    have pointExcess : (target state).toReal - factor * (source state).toReal ≤ 1 - factor := by
      simpa only [PMF.toOuterMeasure_apply_singleton] using
        probOf_domination_excess source target factor lower {state}
    exact ratio_domination_bound _ _ _ _ _ sourcePositive targetPositive
      ENNReal.toReal_nonneg pointWithin positive atMostOne (lower state) pointExcess
      (probOf_domination source target factor lower event)
      (probOf_domination_excess source target factor lower event)
  · rw [ite_eq_right member, ite_eq_right member, sub_self, abs_zero]
    exact div_nonneg (sub_nonneg.mpr atMostOne) (mul_pos positive sourcePositive).le

/-- A vanishing relative loss transports conditioned laws without any lower
bound on the limiting probability of the conditioning event. -/
theorem conditional_domination_converges {State : Type*} [Finite State]
    (source target : ℕ → PMF State) (event : Set State)
    (sourceMeet : ∀ n, ∃ state ∈ event, state ∈ (source n).support)
    (targetMeet : ∀ n, ∃ state ∈ event, state ∈ (target n).support)
    (factor : ℕ → ℝ) (positive : ∀ n, 0 < factor n) (atMostOne : ∀ n, factor n ≤ 1)
    (lower : ∀ n state, factor n * ((source n) state).toReal ≤ ((target n) state).toReal)
    (negligible : Tendsto (fun n =>
      (1 - factor n) / (factor n * ((source n).toOuterMeasure event).toReal)) atTop (nhds 0))
    (limit : PMF State)
    (converges : PMFConvergesPointwise
      (fun n => (source n).filter event (sourceMeet n)) limit) :
    PMFConvergesPointwise (fun n => (target n).filter event (targetMeet n)) limit := by
  rw [pmfConvergesPointwise_iff_toReal]
  intro state
  apply (converges.toReal state).congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ negligible
  intro n
  simpa only [Real.dist_eq, abs_sub_comm] using
    conditional_domination_bound (source n) (target n) event
      (sourceMeet n) (targetMeet n) (factor n) (positive n) (atMostOne n) (lower n) state

end GameTheory.Math.Probability
