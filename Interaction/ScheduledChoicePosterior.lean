/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ScheduledOpeningPosterior
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Timing posteriors for a scheduled binary choice

A selected opportunity can itself draw silence. Observing a replay therefore
retains that past timing slot with the probability of the silent source choice.
The update uses the actual recorded response and its conditional likelihood.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

private theorem posterior_point {Index : Type} (initial : PMF Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (positive : 0 < ((((app.policyMixture initial policies).posterior past).bind
      (fun index => policies index past entry.beforeView)) entry.action).toReal) (index : Index) :
    (((app.policyMixture initial policies).posterior (past ++ [entry])) index).toReal =
      (((app.policyMixture initial policies).posterior past) index).toReal *
        ((policies index past entry.beforeView) entry.action).toReal /
          ((((app.policyMixture initial policies).posterior past).bind
            (fun index => policies index past entry.beforeView)) entry.action).toReal := by
  classical
  let prior := (app.policyMixture initial policies).posterior past
  let joint := prior.bind fun selected =>
    (policies selected past entry.beforeView).map fun response => (response, selected)
  have marginal : joint.map Prod.fst = prior.bind
      (fun selected => policies selected past entry.beforeView) := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact bind_congr_on_support _ fun _ _ => PMF.map_id _
  have meets : ∃ pair ∈ Prod.fst ⁻¹' {entry.action}, pair ∈ joint.support := by
    obtain ⟨pair, supported, same⟩ := PMF.support_map .. ▸
      pmf_toReal_pos_iff.mp (marginal.symm ▸ positive)
    exact ⟨pair, same, supported⟩
  have reconstruct : (joint.filter (Prod.fst ⁻¹' {entry.action}) meets).map
      (fun pair => (entry.action, pair.2)) = joint.filter (Prod.fst ⁻¹' {entry.action}) meets := by
    conv_rhs => rw [← PMF.map_id (joint.filter _ meets)]
    apply map_congr_on_support _
    intro pair supported
    have same := ((PMF.mem_support_filter_iff _).mp supported).1
    exact Prod.ext same.symm rfl
  have reconstructed : ((joint.filter (Prod.fst ⁻¹' {entry.action}) meets).map Prod.snd).map
      (fun selected => (entry.action, selected)) =
        joint.filter (Prod.fst ⁻¹' {entry.action}) meets := by
    rw [PMF.map_comp]
    exact reconstruct
  have point := congrArg (fun law => (law (entry.action, index)).toReal) reconstructed
  rw [pmf_map_apply_of_injective _ (fun _ _ equal => (Prod.mk.inj equal).2)] at point
  rw [Implementation.posterior_snoc]
  change (((fiberConditional joint Prod.fst entry.action).map Prod.snd) index).toReal = _
  rw [fiberConditional, dite_eq_left meets, point, toReal_filter_apply,
    ite_eq_left (show (entry.action, index) ∈ Prod.fst ⁻¹' {entry.action} from rfl),
    ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton, marginal]
  congr 1
  rw [bind_map_tag_apply, ENNReal.toReal_mul]

/-- Updating after one replay downweights precisely the selected timing slot.
All observation-dependent replay probabilities cancel. -/
theorem scheduledChoice_posterior_step {slots : Nat}
    (timing : PMF (Fin slots)) (policies : Fin slots → app.Policy)
    (probability : ℝ) (nonnegative : 0 ≤ probability) (small : probability < 1)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (current : Fin slots)
    (waiting : PMF app.Action) (possible : entry.action ∈ waiting.support)
    (likelihood : ∀ selected,
      ((policies selected past entry.beforeView) entry.action).toReal =
        (if selected = current then 1 - probability else 1) * (waiting entry.action).toReal)
    (old : ∀ selected, (((app.policyMixture timing policies).posterior past) selected).toReal =
      (timing selected).toReal * (if selected.val < current.val then 1 - probability else 1) /
        PMF.deferredSurvival probability timing current.val) :
    ∀ selected,
      (((app.policyMixture timing policies).posterior (past ++ [entry])) selected).toReal =
      (timing selected).toReal * (if selected.val < current.val + 1 then 1 - probability else 1) /
        PMF.deferredSurvival probability timing (current.val + 1) := by
  classical
  let prior := (app.policyMixture timing policies).posterior past
  let mass :=
    ((prior.bind fun selected => policies selected past entry.beforeView) entry.action).toReal
  have massEq : mass = (waiting entry.action).toReal *
      (1 - probability * (prior current).toReal) := by
    dsimp only [mass]
    rw [toReal_bind_apply]
    calc
      _ = expect prior (fun selected => (waiting entry.action).toReal *
          (1 - probability * (if current = selected then 1 else 0))) := by
        apply expect_congr_on_support
        intro selected _
        rw [likelihood]
        by_cases same : selected = current <;> simp [same, Ne.symm, mul_comm]
      _ = _ := by
        rw [expect_const_mul,
          expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
          expect_constant, expect_const_mul, expect_ite_eq, mul_one]
  have denominator := PMF.deferredSurvival_positive probability nonnegative small
    timing current.val
  have nextDenominator := PMF.deferredSurvival_positive probability nonnegative small
    timing (current.val + 1)
  have priorCurrent : (prior current).toReal = (timing current).toReal /
      PMF.deferredSurvival probability timing current.val := by
    simpa only [lt_self_iff_false, ↓reduceIte, mul_one] using old current
  have massValue : mass = (waiting entry.action).toReal *
      PMF.deferredSurvival probability timing (current.val + 1) /
        PMF.deferredSurvival probability timing current.val := by
    rw [massEq, priorCurrent, PMF.deferredSurvival_succ]
    field_simp
  have positive : 0 < mass := by
    rw [massValue]
    exact div_pos (mul_pos (pmf_toReal_pos_iff.mpr possible) nextDenominator) denominator
  intro selected
  rw [app.posterior_point timing policies past entry positive selected, likelihood, old]
  change _ / mass = _
  rw [massValue]
  have factors :
      (if selected.val < current.val then 1 - probability else 1) *
          (if selected = current then 1 - probability else 1) =
        (if selected.val < current.val + 1 then 1 - probability else 1) := by
    by_cases same : selected = current
    · subst selected
      simp
    · have unequal : selected.val ≠ current.val := fun equal => same (Fin.ext equal)
      by_cases earlier : selected.val < current.val
      · simp [same, earlier, show selected.val < current.val + 1 by omega]
      · simp [same, earlier, show ¬ selected.val < current.val + 1 by omega]
  field_simp [ne_of_gt denominator, ne_of_gt nextDenominator,
    ne_of_gt (pmf_toReal_pos_iff.mpr possible)]
  simpa only [mul_assoc] using congrArg (fun value => (timing selected).toReal * value) factors

/-- The mass of timing choices that can still open gives exactly the deferred
source probability. Past silent choices remain in the denominator. -/
theorem scheduledChoice_remaining_probability {slots : Nat}
    (timing posterior : PMF (Fin slots)) (probability : ℝ) (count : Nat)
    (points : ∀ slot, (posterior slot).toReal =
      (timing slot).toReal * (if slot.val < count then 1 - probability else 1) /
        PMF.deferredSurvival probability timing count) :
    probability * (posterior.toOuterMeasure {slot | count ≤ slot.val}).toReal =
      PMF.deferredRemaining probability timing count := by
  classical
  have total : (∑ slot : Fin slots, if count ≤ slot.val then (timing slot).toReal else 0) =
      1 - timing.timingPrefix count := by
    rw [← pmf_sum_toReal_eq_one timing, PMF.timingPrefix, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro slot _
    by_cases before : slot.val < count
    · simp only [before, Nat.not_le.mpr before, ↓reduceIte, sub_self]
    · simp only [before, Nat.le_of_not_gt before, ↓reduceIte, sub_zero]
  have mass : (posterior.toOuterMeasure {slot | count ≤ slot.val}).toReal =
      (1 - timing.timingPrefix count) / PMF.deferredSurvival probability timing count := by
    rw [← expect_indicator, expect_eq_sum, ← total]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro slot _
    rw [points]
    by_cases before : slot.val < count
    · simp only [Set.mem_ofPred_eq, before, Nat.not_le.mpr before, ↓reduceIte,
        mul_zero, zero_mul]
    · simp only [Set.mem_ofPred_eq, before, Nat.le_of_not_gt before, ↓reduceIte, mul_one,
        div_eq_mul_inv]
  rw [mass, PMF.deferredRemaining]
  ring

end Interaction.ReactiveApplication
