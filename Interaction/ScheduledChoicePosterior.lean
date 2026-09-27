/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ScheduledOpeningPosterior

/-! # Timing posteriors for a scheduled binary choice

A selected opportunity can itself draw silence. Observing a replay therefore
retains that past timing slot with the probability of the silent source choice.
The update uses the actual recorded response and its conditional likelihood.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

private theorem posterior_point {Index : Type} (initial : FinDist Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (positive : 0 < (((app.policyMixture initial policies).posterior past).bind
      (fun index => policies index past entry.beforeView)).prob entry.action) (index : Index) :
    ((app.policyMixture initial policies).posterior (past ++ [entry])).prob index =
      ((app.policyMixture initial policies).posterior past).prob index *
        (policies index past entry.beforeView).prob entry.action /
          (((app.policyMixture initial policies).posterior past).bind
            (fun index => policies index past entry.beforeView)).prob entry.action := by
  classical
  let prior := (app.policyMixture initial policies).posterior past
  let joint := prior.bind fun selected =>
    (policies selected past entry.beforeView).map fun response => (response, selected)
  have marginal : joint.map Prod.fst = prior.bind
      (fun selected => policies selected past entry.beforeView) := by
    simp only [joint, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
    exact FinDist.bind_congr fun _ _ => FinDist.map_id _
  have meets : ∃ pair ∈ Prod.fst ⁻¹' {entry.action}, pair ∈ joint.support := by
    obtain ⟨pair, supported, same⟩ := FinDist.support_map .. ▸
      FinDist.prob_pos_iff.mp (marginal.symm ▸ positive)
    exact ⟨pair, same, supported⟩
  have reconstruct : (joint.condOn (Prod.fst ⁻¹' {entry.action}) meets).map
      (fun pair => (entry.action, pair.2)) = joint.condOn (Prod.fst ⁻¹' {entry.action}) meets := by
    conv_rhs => rw [← FinDist.map_id (joint.condOn _ meets)]
    apply FinDist.map_congr_of_eq_on_support
    intro pair supported
    have same := (FinDist.support_condOn _ _ _ supported).1
    exact Prod.ext same.symm rfl
  have reconstructed : ((joint.condOn (Prod.fst ⁻¹' {entry.action}) meets).map Prod.snd).map
      (fun selected => (entry.action, selected)) =
        joint.condOn (Prod.fst ⁻¹' {entry.action}) meets := by
    rw [FinDist.map_comp]
    exact reconstruct
  have point := congrArg (fun law => law.prob (entry.action, index)) reconstructed
  rw [FinDist.prob_map_of_injective (fun selected => (entry.action, selected))
      (fun _ _ equal => (Prod.mk.inj equal).2)] at point
  rw [Implementation.posterior_snoc]
  change ((joint.condOnFibre Prod.fst entry.action).map Prod.snd).prob index = _
  rw [FinDist.condOnFibre, dite_eq_left meets, point, FinDist.prob_condOn,
    ite_eq_left (show (entry.action, index) ∈ Prod.fst ⁻¹' {entry.action} from rfl),
    ← FinDist.prob_map_eq_probOf_preimage_singleton, marginal]
  congr 1
  rw [FinDist.prob_bind_of_unique_branch prior
    (fun selected => (policies selected past entry.beforeView).map
      fun response => (response, selected)) (entry.action, index) index]
  · rw [FinDist.prob_map_of_injective (fun response : app.Action => (response, index))
      (fun _ _ same => (Prod.mk.inj same).1)]
  · intro selected _ supported
    obtain ⟨response, _, same⟩ := FinDist.support_map .. ▸ supported
    exact congrArg Prod.snd same

/-- Updating after one replay downweights precisely the selected timing slot.
All observation-dependent replay probabilities cancel. -/
theorem scheduledChoice_posterior_step {slots : Nat}
    (timing : FinDist (Fin slots)) (policies : Fin slots → app.Policy)
    (probability : ℝ) (nonnegative : 0 ≤ probability) (small : probability < 1)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (current : Fin slots)
    (waiting : FinDist app.Action) (possible : entry.action ∈ waiting.support)
    (likelihood : ∀ selected,
      (policies selected past entry.beforeView).prob entry.action =
        (if selected = current then 1 - probability else 1) * waiting.prob entry.action)
    (old : ∀ selected, ((app.policyMixture timing policies).posterior past).prob selected =
      timing.prob selected * (if selected.val < current.val then 1 - probability else 1) /
        FinDist.deferredSurvival probability timing current.val) :
    ∀ selected, ((app.policyMixture timing policies).posterior (past ++ [entry])).prob selected =
      timing.prob selected * (if selected.val < current.val + 1 then 1 - probability else 1) /
        FinDist.deferredSurvival probability timing (current.val + 1) := by
  classical
  let prior := (app.policyMixture timing policies).posterior past
  let mass := (prior.bind fun selected => policies selected past entry.beforeView).prob entry.action
  have massEq : mass = waiting.prob entry.action *
      (1 - probability * prior.prob current) := by
    dsimp only [mass]
    rw [FinDist.prob_bind]
    calc
      _ = prior.expect (fun selected => waiting.prob entry.action *
          (1 - probability * (if current = selected then 1 else 0))) := by
        apply FinDist.expect_congr
        intro selected _
        rw [likelihood]
        by_cases same : selected = current <;> simp [same, Ne.symm, mul_comm]
      _ = _ := by
        rw [FinDist.expect_smul, FinDist.expect_sub, FinDist.expect_const,
          FinDist.expect_smul, FinDist.expect_ite_eq, mul_one]
  have denominator := FinDist.deferredSurvival_positive probability nonnegative small
    timing current.val
  have nextDenominator := FinDist.deferredSurvival_positive probability nonnegative small
    timing (current.val + 1)
  have priorCurrent : prior.prob current = timing.prob current /
      FinDist.deferredSurvival probability timing current.val := by
    simpa only [lt_self_iff_false, ↓reduceIte, mul_one] using old current
  have massValue : mass = waiting.prob entry.action *
      FinDist.deferredSurvival probability timing (current.val + 1) /
        FinDist.deferredSurvival probability timing current.val := by
    rw [massEq, priorCurrent, FinDist.deferredSurvival_succ]
    field_simp
  have positive : 0 < mass := by
    rw [massValue]
    exact div_pos (mul_pos (FinDist.prob_pos_iff.mpr possible) nextDenominator) denominator
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
    ne_of_gt (FinDist.prob_pos_iff.mpr possible)]
  simpa only [mul_assoc] using congrArg (fun value => timing.prob selected * value) factors

/-- The mass of timing choices that can still open gives exactly the deferred
source probability. Past silent choices remain in the denominator. -/
theorem scheduledChoice_remaining_probability {slots : Nat}
    (timing posterior : FinDist (Fin slots)) (probability : ℝ) (count : Nat)
    (points : ∀ slot, posterior.prob slot =
      timing.prob slot * (if slot.val < count then 1 - probability else 1) /
        FinDist.deferredSurvival probability timing count) :
    probability * posterior.probOf {slot | count ≤ slot.val} =
      FinDist.deferredRemaining probability timing count := by
  classical
  have total : (∑ slot : Fin slots, if count ≤ slot.val then timing.prob slot else 0) =
      1 - timing.timingPrefix count := by
    rw [← timing.sum_prob, FinDist.timingPrefix, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro slot _
    by_cases before : slot.val < count
    · simp only [before, Nat.not_le.mpr before, ↓reduceIte, sub_self]
    · simp only [before, Nat.le_of_not_gt before, ↓reduceIte, sub_zero]
  have mass : posterior.probOf {slot | count ≤ slot.val} =
      (1 - timing.timingPrefix count) / FinDist.deferredSurvival probability timing count := by
    rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_eq_sum, ← total]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro slot _
    rw [points]
    by_cases before : slot.val < count
    · simp only [Set.mem_ofPred_eq, before, Nat.not_le.mpr before, ↓reduceIte,
        mul_zero, zero_mul]
    · simp only [Set.mem_ofPred_eq, before, Nat.le_of_not_gt before, ↓reduceIte, mul_one,
        div_eq_mul_inv]
  rw [mass, FinDist.deferredRemaining]
  ring

end Interaction.ReactiveApplication
