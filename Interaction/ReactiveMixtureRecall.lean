/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyMixture
import Interaction.ReactiveRecovery

/-! # Possible policy members agree with the actual supported own recall -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal) {Index : Type}

/-- Every member still possible after a genuinely supported own transcript
supports every remembered response at its original full input. -/
theorem policyMixture_member_consistent (initial : PMF Index) (family : Index → app.Policy)
    (past : List app.PlayerEntry)
    (consistent : (app.policyMixture initial family).policy.Consistent past)
    (index : Index)
    (supported : index ∈ ((app.policyMixture initial family).posterior past).support) :
    (family index).Consistent past := by
  induction consistent generalizing index with
  | nil => exact .nil
  | @snoc earlier entry prior sampled ih =>
      obtain ⟨saved, previous, produced⟩ :=
        (app.policyMixture initial family).mem_support_posterior_snoc earlier entry sampled index
          supported
      obtain ⟨action, allowed, equal⟩ := PMF.support_map .. ▸ produced
      have savedEq : saved = index := congrArg Prod.snd equal
      subst saved
      have actionEq : action = entry.action := congrArg Prod.fst equal
      exact .snoc entry (ih index previous) (actionEq ▸ allowed)


open Classical in
private theorem posterior_snoc_filter (initial : PMF Index) (family : Index → app.Policy)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (kept : Set Index)
    (meets : ∃ index ∈ kept, index ∈ ((app.policyMixture initial family).posterior past).support)
    (likelihood : ENNReal) (positive : likelihood ≠ 0) (finite : likelihood ≠ ⊤)
    (atoms : ∀ index ∈ ((app.policyMixture initial family).posterior past).support,
      family index past entry.beforeView entry.action = if index ∈ kept then likelihood else 0) :
    (app.policyMixture initial family).posterior (past ++ [entry]) =
      ((app.policyMixture initial family).posterior past).filter kept meets := by
  classical
  let prior := (app.policyMixture initial family).posterior past
  let branch := fun index => family index past entry.beforeView
  let joint := prior.bind fun index => (branch index).map fun action => (action, index)
  have jointAt (index : Index) : joint (entry.action, index) =
      kept.indicator prior index * likelihood := by
    rw [bind_map_tag_apply]
    by_cases supported : index ∈ prior.support
    · rw [atoms index supported]
      by_cases retained : index ∈ kept
      · rw [ite_eq_left retained, Set.indicator_of_mem retained]
      · rw [ite_eq_right retained, Set.indicator_of_notMem retained, mul_zero, zero_mul]
    · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
      rw [zero, zero_mul]
      by_cases retained : index ∈ kept
      · rw [Set.indicator_of_mem retained, zero, zero_mul]
      · rw [Set.indicator_of_notMem retained, zero_mul]
  have marginal : (joint.map Prod.fst) entry.action =
      (∑' index, kept.indicator prior index) * likelihood := by
    have projected : joint.map Prod.fst = prior.bind branch := by
      simp only [joint, PMF.map_bind, PMF.map_comp]
      exact bind_congr_on_support _ fun _ _ => PMF.map_id _
    rw [projected, PMF.bind_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro index
    exact (bind_map_tag_apply prior branch entry.action index).symm.trans (jointAt index)
  have present : entry.action ∈ (joint.map Prod.fst).support := by
    obtain ⟨index, retained, supported⟩ := meets
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨(entry.action, index), ?_, rfl⟩
    rw [PMF.mem_support_iff, jointAt, Set.indicator_of_mem retained]
    exact mul_ne_zero ((PMF.mem_support_iff ..).mp supported) positive
  rw [Implementation.posterior_snoc]
  change (fiberPosterior joint Prod.fst entry.action).map Prod.snd = _
  ext index
  rw [fiberPosterior_map_snd_apply joint entry.action present, jointAt, marginal, PMF.filter_apply]
  rw [ENNReal.mul_inv (Or.inr finite) (Or.inr positive)]
  calc
    kept.indicator prior index * likelihood *
        ((∑' index, kept.indicator prior index)⁻¹ * likelihood⁻¹) =
        kept.indicator prior index * (∑' index, kept.indicator prior index)⁻¹ *
          (likelihood * likelihood⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel positive finite, mul_one]

/-- When all members supporting a recorded reply give it the same mass,
conditioning the immutable member on its full own recall restricts the original
prior exactly to members consistent with that recall. Positive admission is
stated for that original prior, including at zero-probability external inputs. -/
theorem policyMixture_posterior_consistent (initial : PMF Index) (family : Index → app.Policy)
    (equalAtoms : ∀ past view action first second,
      action ∈ (family first past view).support → action ∈ (family second past view).support →
        family first past view action = family second past view action)
    (past : List app.PlayerEntry)
    (positive : ∃ index ∈ {index | (family index).Consistent past}, index ∈ initial.support) :
    (app.policyMixture initial family).posterior past =
      initial.filter {index | (family index).Consistent past} positive := by
  classical
  induction past using List.reverseRecOn with
  | nil =>
      change initial = _
      exact (filter_of_support_subset initial _ positive (fun _ _ => .nil)).symm
  | append_singleton past entry ih =>
      let earlier : Set Index := {index | (family index).Consistent past}
      let full : Set Index := {index | (family index).Consistent (past ++ [entry])}
      have included : full ⊆ earlier := fun index supported =>
        ((family index).consistent_snoc_iff past entry).mp supported |>.1
      have earlierPositive : ∃ index ∈ earlier, index ∈ initial.support := by
        obtain ⟨index, compatible, supported⟩ := positive
        exact ⟨index, included compatible, supported⟩
      have previous := ih earlierPositive
      let prior := (app.policyMixture initial family).posterior past
      have nextPositive : ∃ index ∈ full, index ∈ prior.support := by
        obtain ⟨index, compatible, supported⟩ := positive
        refine ⟨index, compatible, ?_⟩
        rw [show prior = initial.filter earlier earlierPositive from previous]
        exact (PMF.mem_support_filter_iff earlierPositive).mpr ⟨included compatible, supported⟩
      have witnessed := nextPositive
      obtain ⟨witness, compatible, _supported⟩ := witnessed
      have witnessSample := ((family witness).consistent_snoc_iff past entry).mp compatible |>.2
      let likelihood := family witness past entry.beforeView entry.action
      have nonzero : likelihood ≠ 0 := (PMF.mem_support_iff ..).mp witnessSample
      have atoms : ∀ index ∈ prior.support,
          family index past entry.beforeView entry.action =
            if index ∈ full then likelihood else 0 := by
        intro index supported
        have old : index ∈ earlier := by
          rw [show prior = initial.filter earlier earlierPositive from previous] at supported
          exact ((PMF.mem_support_filter_iff earlierPositive).mp supported).1
        by_cases retained : index ∈ full
        · rw [ite_eq_left retained]
          exact equalAtoms past entry.beforeView entry.action index witness
            (((family index).consistent_snoc_iff past entry).mp retained |>.2) witnessSample
        · rw [ite_eq_right retained]
          apply (PMF.apply_eq_zero_iff _ _).mpr
          intro sampled
          exact retained (((family index).consistent_snoc_iff past entry).mpr ⟨old, sampled⟩)
      rw [app.posterior_snoc_filter initial family past entry full nextPositive likelihood nonzero
        (PMF.apply_ne_top _ _) atoms]
      have next : ∃ index ∈ full, index ∈ (initial.filter earlier earlierPositive).support := by
        simpa only [prior, previous] using nextPositive
      have nested := filter_filter_of_subset initial earlier full earlierPositive next included
      simpa only [earlier, full, ← previous] using nested


/-- Immutable policy selection preserves its original support at every
supported own recall. This is a property of the actual private implementation,
not of any external history likelihood. -/
theorem policyMixture_posterior_mem_initial (initial : PMF Index) (family : Index → app.Policy)
    (past : List app.PlayerEntry)
    (consistent : (app.policyMixture initial family).policy.Consistent past)
    (index : Index)
    (supported : index ∈ ((app.policyMixture initial family).posterior past).support) :
    index ∈ initial.support := by
  induction consistent generalizing index with
  | nil => exact supported
  | @snoc earlier entry previous sampled ih =>
      obtain ⟨saved, retained, produced⟩ :=
        (app.policyMixture initial family).mem_support_posterior_snoc earlier entry sampled index
          supported
      obtain ⟨_action, _allowed, equal⟩ := PMF.support_map .. ▸ produced
      have unchanged : saved = index := congrArg Prod.snd equal
      exact ih index (unchanged ▸ retained)

open Classical in
/-- At a supported behavioral own recall, equal supported atoms turn the
original immutable-member prior into its exact consistency fiber. Positivity
of this original fiber follows from the actual implementation support. -/
theorem policyMixture_posterior_consistency_fiber (initial : PMF Index)
    (family : Index → app.Policy)
    (equalAtoms : ∀ past view action first second,
      action ∈ (family first past view).support → action ∈ (family second past view).support →
        family first past view action = family second past view action)
    (past : List app.PlayerEntry)
    (consistent : (app.policyMixture initial family).policy.Consistent past) :
    (app.policyMixture initial family).posterior past =
      fiberPosterior initial (fun index => decide ((family index).Consistent past)) true := by
  classical
  obtain ⟨index, supported⟩ := ((app.policyMixture initial family).posterior past).support_nonempty
  have admitted := app.policyMixture_posterior_mem_initial initial family past consistent index
    supported
  have member := app.policyMixture_member_consistent initial family past consistent index supported
  have positive : ∃ index ∈ {index | (family index).Consistent past}, index ∈ initial.support :=
    ⟨index, member, admitted⟩
  rw [app.policyMixture_posterior_consistent initial family equalAtoms past positive]
  have meets : ∃ index ∈ {index | decide ((family index).Consistent past) = true},
      index ∈ initial.support :=
    ⟨index, by simpa only [Set.mem_ofPred_eq, decide_eq_true_eq] using member, admitted⟩
  rw [fiberPosterior_eq_filter initial _ meets]
  congr 1
  ext word
  exact decide_eq_true_iff.symm

end Interaction.ReactiveApplication
