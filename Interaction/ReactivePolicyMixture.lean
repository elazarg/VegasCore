/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveImplementation
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Behavioral realization of a finite family of response policies

A latent choice selects an existing response policy. Its behavioral realization
conditions that choice on actual own recall. This adds no state to the runtime;
the implementation is the existing private-strategy construction.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal) {Index : Type}

def policyMixture (initial : PMF Index) (policies : Index → app.Policy) :
    app.Implementation Index where
  initial := initial
  respond index input := (policies index input.1 input.2).map fun action => (action, index)

theorem policyMixture_policy (initial : PMF Index) (policies : Index → app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (app.policyMixture initial policies).policy past view =
      ((app.policyMixture initial policies).posterior past).bind
        (fun index => policies index past view) := by
  simp only [Implementation.policy_eq, policyMixture, PMF.map_bind,
    PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro index _
  exact PMF.map_id _

/-- A response whose law does not use the latent choice cannot update it. -/
theorem policyMixture_posterior_snoc (initial : PMF Index) (policies : Index → app.Policy)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (law : PMF app.Action)
    (same : ∀ index, policies index past entry.beforeView = law) :
    (app.policyMixture initial policies).posterior (past ++ [entry]) =
      (app.policyMixture initial policies).posterior past := by
  rw [Implementation.posterior_snoc]
  change (fiberPosterior (((app.policyMixture initial policies).posterior past).bind
    (fun index => (policies index past entry.beforeView).map fun action => (action, index)))
      Prod.fst entry.action).map Prod.snd = _
  have joint : ((app.policyMixture initial policies).posterior past).bind
      (fun index => (policies index past entry.beforeView).map fun action => (action, index)) =
        bindPairLaw law (fun _ => ((app.policyMixture initial policies).posterior past)) := by
    simp_rw [same, ← PMF.bind_pure_comp, Function.comp_def]
    rw [PMF.bind_comm]
    rfl
  rw [joint, fiberPosterior_snd_bindPairLaw_const]

/-- A response that every member still possible gives with one common positive
probability cannot update the latent choice. -/
theorem policyMixture_posterior_snoc_of_likelihood (initial : PMF Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (likelihood : ENNReal)
    (same : ∀ index ∈ ((app.policyMixture initial policies).posterior past).support,
      policies index past entry.beforeView entry.action = likelihood)
    (positive : likelihood ≠ 0) :
    (app.policyMixture initial policies).posterior (past ++ [entry]) =
      (app.policyMixture initial policies).posterior past := by
  set prior := (app.policyMixture initial policies).posterior past
  rw [Implementation.posterior_snoc]
  change (fiberPosterior (prior.bind fun index =>
    (policies index past entry.beforeView).map fun action => (action, index))
      Prod.fst entry.action).map Prod.snd = prior
  set joint := prior.bind fun index =>
    (policies index past entry.beforeView).map fun action => (action, index)
  have swapped : joint = (bindPairLaw prior fun index => policies index past entry.beforeView).map
      Prod.swap := by
    simp only [joint, bindPairLaw, PMF.map_bind, PMF.map_comp]
    rfl
  have jointApply (action : app.Action) (index : Index) :
      joint (action, index) = prior index * policies index past entry.beforeView action := by
    rw [swapped, show ((action, index) : app.Action × Index) = Prod.swap (index, action) from rfl,
      pmf_map_apply_of_injective _ Prod.swap_injective, bindPairLaw_apply]
  have marginal : (joint.map Prod.fst) entry.action = likelihood := by
    have projected : joint.map Prod.fst =
        prior.bind fun index => policies index past entry.beforeView := by
      simp only [joint, PMF.map_bind, PMF.map_comp]
      exact bind_congr_on_support _ fun _ _ => PMF.map_id _
    rw [projected, PMF.bind_apply]
    calc (∑' index, prior index * policies index past entry.beforeView entry.action) =
          ∑' index, prior index * likelihood := by
          refine tsum_congr fun index => ?_
          by_cases member : index ∈ prior.support
          · rw [same index member]
          · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]
      _ = likelihood := by rw [ENNReal.tsum_mul_right, prior.tsum_coe, one_mul]
  have present : entry.action ∈ (joint.map Prod.fst).support := by
    rw [PMF.mem_support_iff, marginal]
    exact positive
  have finite : likelihood ≠ ⊤ := by
    rw [← marginal]
    exact PMF.apply_ne_top _ _
  ext index
  rw [fiberPosterior_map_snd_apply joint entry.action present index, jointApply, marginal]
  by_cases member : index ∈ prior.support
  · rw [same index member, mul_assoc, ENNReal.mul_inv_cancel positive finite, mul_one]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

/-- A policy family that agrees with one policy at every recorded response
retains its initial mixing law, including at zero-probability own transcripts. -/
theorem policyMixture_posterior_of_agree (initial : PMF Index)
    (policies : Index → app.Policy) (baseline : app.Policy) (past : List app.PlayerEntry)
    (agree : ∀ (before : List app.PlayerEntry) (entry : app.PlayerEntry),
      before ++ [entry] <+: past → ∀ index,
        policies index before entry.beforeView = baseline before entry.beforeView) :
    (app.policyMixture initial policies).posterior past = initial := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [app.policyMixture_posterior_snoc initial policies past entry
        (baseline past entry.beforeView) (agree past entry (List.prefix_refl _))]
      exact ih fun before earlier member =>
        agree before earlier (member.trans (List.prefix_append _ _))

/-- A policy family that is identical before a phase retains its initial
mixing law at that phase, including at zero-probability own transcripts. -/
theorem policyMixture_posterior_dormant (initial : PMF Index)
    (policies : Index → app.Policy) (baseline : app.Policy) (offset : Nat)
    (same : ∀ index past view, past.length < offset →
      policies index past view = baseline past view)
    (past : List app.PlayerEntry) (before : past.length ≤ offset) :
    (app.policyMixture initial policies).posterior past = initial :=
  app.policyMixture_posterior_of_agree initial policies baseline past
    fun earlier entry member index => same index _ _ (by
      have length := member.length_le
      simp only [List.length_append, List.length_singleton] at length
      omega)

/-- Select a single opportunity by its index. `turn past view` is the index of
the current input among the opportunities, read from the actual recall and
view, or `none` when the input is not an opportunity. The selected opportunity
uses `opening`; every other response, including later opportunities, uses
`waiting`. -/
def turnScheduledPolicy (turn : List app.PlayerEntry → app.PlayerView → Option Nat)
    {slots : Nat} (selected : Option (Fin slots)) (opening waiting : app.Policy) :
    app.Policy := fun past view =>
  match selected with
  | none => waiting past view
  | some slot => if turn past view = some slot.val then opening past view else waiting past view

/-- An input that is not an opportunity waits under every selection. -/
theorem turnScheduledPolicy_of_none (turn : List app.PlayerEntry → app.PlayerView → Option Nat)
    {slots : Nat} (selected : Option (Fin slots)) (opening waiting : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView) (idle : turn past view = none) :
    app.turnScheduledPolicy turn selected opening waiting past view = waiting past view := by
  cases selected with
  | none => rfl
  | some slot => simp only [turnScheduledPolicy, idle, reduceCtorEq, ↓reduceIte]

/-- The selected opportunity opens. -/
theorem turnScheduledPolicy_selected (turn : List app.PlayerEntry → app.PlayerView → Option Nat)
    {slots : Nat} (slot : Fin slots) (opening waiting : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (current : turn past view = some slot.val) :
    app.turnScheduledPolicy turn (some slot) opening waiting past view = opening past view := by
  simp only [turnScheduledPolicy, current, ↓reduceIte]

/-- Every other opportunity waits. -/
theorem turnScheduledPolicy_unselected
    (turn : List app.PlayerEntry → app.PlayerView → Option Nat)
    {slots : Nat} (selected : Option (Fin slots)) (opening waiting : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (other : ∀ slot, selected = some slot → turn past view ≠ some slot.val) :
    app.turnScheduledPolicy turn selected opening waiting past view = waiting past view := by
  cases selected with
  | none => rfl
  | some slot => simp only [turnScheduledPolicy, other slot rfl, ↓reduceIte]

/-- Select a single owner opportunity using its actual response count. Every
other response uses the supplied policy, including after the selected visit. -/
def scheduledPolicy (offset : Nat) {slots : Nat} (selected : Option (Fin slots))
    (opening waiting : app.Policy) : app.Policy := fun past view =>
  if selected.map (fun slot => offset + slot.val) = some past.length then
    opening past view else waiting past view

/-- The opportunity index of a response count past `offset`. -/
def countFrom (offset : Nat) (past : List app.PlayerEntry) (_view : app.PlayerView) :
    Option Nat :=
  if offset ≤ past.length then some (past.length - offset) else none

/-- Counting responses from an offset is one way of indexing opportunities. -/
theorem scheduledPolicy_eq_turnScheduledPolicy (offset : Nat) {slots : Nat}
    (selected : Option (Fin slots)) (opening waiting : app.Policy) :
    app.scheduledPolicy offset selected opening waiting =
      app.turnScheduledPolicy (app.countFrom offset) selected opening waiting := by
  funext past view
  cases selected with
  | none => simp [scheduledPolicy, turnScheduledPolicy]
  | some slot =>
      simp only [scheduledPolicy, turnScheduledPolicy, countFrom, Option.map_some,
        Option.some.injEq]
      by_cases within : offset ≤ past.length
      · simp only [within, ↓reduceIte, Option.some.injEq]
        by_cases equal : offset + slot.val = past.length
        · simp only [equal, show past.length - offset = slot.val by omega, ↓reduceIte]
        · simp only [equal, show ¬ past.length - offset = slot.val by omega, ↓reduceIte]
      · simp only [within, ↓reduceIte, reduceCtorEq,
          show ¬ offset + slot.val = past.length by omega]

theorem scheduledPolicy_before (offset : Nat) {slots : Nat}
    (selected : Option (Fin slots)) (opening waiting : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView) (before : past.length < offset) :
    app.scheduledPolicy offset selected opening waiting past view = waiting past view := by
  rw [scheduledPolicy_eq_turnScheduledPolicy]
  exact app.turnScheduledPolicy_of_none _ selected opening waiting past view
    (by simp only [countFrom, Nat.not_le.mpr before, ↓reduceIte])

/-- Two mixtures with one initial law have the same posterior on a recall
where, at every entry, either their members respond alike index by index, or
each family responds without using the latent choice. -/
theorem policyMixture_posterior_congr (initial : PMF Index) (first second : Index → app.Policy)
    (past : List app.PlayerEntry)
    (step : ∀ (before : List app.PlayerEntry) (entry : app.PlayerEntry),
      before ++ [entry] <+: past →
        (∀ index, first index before entry.beforeView = second index before entry.beforeView) ∨
          ((∃ law, ∀ index, first index before entry.beforeView = law) ∧
            ∃ law, ∀ index, second index before entry.beforeView = law)) :
    (app.policyMixture initial first).posterior past =
      (app.policyMixture initial second).posterior past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier := ih fun before earlier member =>
        step before earlier (member.trans (List.prefix_append _ _))
      rcases step past entry (List.prefix_refl _) with alike | ⟨⟨firstLaw, firstSame⟩,
          ⟨secondLaw, secondSame⟩⟩
      · rw [Implementation.posterior_snoc, Implementation.posterior_snoc, earlier]
        change (fiberPosterior (((app.policyMixture initial second).posterior past).bind
          (fun index => (first index past entry.beforeView).map fun action => (action, index)))
            Prod.fst entry.action).map Prod.snd =
          (fiberPosterior (((app.policyMixture initial second).posterior past).bind
          (fun index => (second index past entry.beforeView).map fun action => (action, index)))
            Prod.fst entry.action).map Prod.snd
        simp only [alike]
      · rw [app.policyMixture_posterior_snoc initial first past entry firstLaw firstSame,
          app.policyMixture_posterior_snoc initial second past entry secondLaw secondSame, earlier]

/-- **A mixture dispatched to one region.** Members that respond as a family
inside a region of inputs and as one common policy outside it, where the family
does not use the latent choice, realize that common policy, provided it
responds inside the region as the family's mixture. -/
theorem policyMixture_policy_of_region (initial : PMF Index)
    (member family : Index → app.Policy) (client : app.Policy)
    (region : List app.PlayerEntry → app.PlayerView → Prop)
    (inside : ∀ index past view, region past view → member index past view = family index past view)
    (outside : ∀ index past view, ¬ region past view → member index past view = client past view)
    (familyOutside : ∀ past view, ¬ region past view →
      ∃ law, ∀ index, family index past view = law)
    (atRegion : ∀ past view, region past view →
      client past view = (app.policyMixture initial family).policy past view)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (app.policyMixture initial member).policy past view = client past view := by
  classical
  have posteriors := app.policyMixture_posterior_congr initial member family past
    fun before entry _ => by
      by_cases within : region before entry.beforeView
      · exact Or.inl fun index => inside index before entry.beforeView within
      · exact Or.inr ⟨⟨client before entry.beforeView, fun index =>
          outside index before entry.beforeView within⟩,
          familyOutside before entry.beforeView within⟩
  rw [app.policyMixture_policy, posteriors]
  by_cases within : region past view
  · simp only [inside _ _ _ within]
    rw [← app.policyMixture_policy, atRegion past view within]
  · simp only [outside _ _ _ within, PMF.bind_const]

private theorem posterior_independent_left {Local Rest Output : Type}
    (first : PMF Local) (joint : PMF (Output × Rest)) (output : Output) :
    (fiberPosterior (first.bind fun value =>
      joint.map (fun result => (result.1, (value, result.2)))) Prod.fst output).map Prod.snd =
      first.bind (fun value => ((fiberPosterior joint Prod.fst output).map Prod.snd).map
        (fun rest => (value, rest))) := by
  let expand := fun result : Output × Rest =>
    first.map (fun value => (result.1, (value, result.2)))
  have swapped : joint.bind expand = first.bind (fun value =>
      joint.map (fun result => (result.1, (value, result.2)))) := by
    simp only [expand, ← PMF.bind_pure_comp, Function.comp_def]
    rw [PMF.bind_comm]
  rw [← swapped]
  by_cases present : output ∈ (joint.map Prod.fst).support
  · have conditional := fiberPosterior_bind_of_observation joint expand Prod.fst Prod.fst
      (fun result _ next member => by
        obtain ⟨value, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        rfl) output present
    rw [conditional]
    simp only [expand, PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp only [← PMF.bind_pure_comp, Function.comp_def]
    rw [PMF.bind_comm]
  · have absent : output ∉ ((joint.bind expand).map Prod.fst).support := by
      intro supported
      obtain ⟨next, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      obtain ⟨result, oldSupport, generated⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      obtain ⟨value, _supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp generated
      exact present ((PMF.mem_support_map_iff _ _ _).mpr
        ⟨result, oldSupport, (congrArg Prod.fst equal).trans same⟩)
    rw [fiberPosterior_of_not_mem_support _ _ absent,
      fiberPosterior_of_not_mem_support _ _ present]
    rw [swapped, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]

/-- A private coordinate absent from every recorded response retains its
original law independently of the complete updated remainder. Responses may
randomize using the remainder; no deterministic-policy assumption is needed. -/
theorem policyMixture_posterior_independent_left {Local Rest : Type}
    (first : PMF Local) (restLaw : PMF Rest)
    (members : Local × Rest → app.Policy) (remainder : Rest → app.Policy)
    (past : List app.PlayerEntry)
    (unread : ∀ (before : List app.PlayerEntry) (entry : app.PlayerEntry),
      before ++ [entry] <+: past → ∀ value rest,
        members (value, rest) before entry.beforeView = remainder rest before entry.beforeView) :
    (app.policyMixture (first.bind fun value => restLaw.map (Prod.mk value))
      members).posterior past =
      first.bind (fun value => ((app.policyMixture restLaw remainder).posterior past).map
        (Prod.mk value)) := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier := ih fun before recorded inside =>
        unread before recorded (inside.trans (List.prefix_append _ _))
      rw [Implementation.posterior_snoc, earlier, Implementation.posterior_snoc]
      change (fiberPosterior ((first.bind fun value =>
        ((app.policyMixture restLaw remainder).posterior past).map (Prod.mk value)).bind
          (fun pair => (members pair past entry.beforeView).map
            (fun response => (response, pair)))) Prod.fst entry.action).map Prod.snd = _
      have jointEq : ((first.bind fun value =>
          ((app.policyMixture restLaw remainder).posterior past).map (Prod.mk value)).bind
            (fun pair => (members pair past entry.beforeView).map
              (fun response => (response, pair)))) =
          first.bind (fun value =>
            (((app.policyMixture restLaw remainder).posterior past).bind fun rest =>
              (remainder rest past entry.beforeView).map (fun response => (response, rest))).map
                (fun response => (response.1, (value, response.2)))) := by
        simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
        apply bind_congr_on_support
        intro value _supported
        apply bind_congr_on_support
        intro rest _possible
        rw [unread past entry (List.prefix_refl _) value rest]
      rw [jointEq, posterior_independent_left]
      rfl

private theorem posterior_map_memory {First Second Output : Type}
    (joint : PMF (Output × First)) (relabel : First → Second) (output : Output) :
    ((fiberPosterior joint Prod.fst output).map Prod.snd).map relabel =
      (fiberPosterior (joint.map (fun pair => (pair.1, relabel pair.2))) Prod.fst output).map
        Prod.snd := by
  by_cases present : output ∈ (joint.map Prod.fst).support
  · have moved := map_fiberPosterior_readout joint
      (fun pair => (pair.1, relabel pair.2)) Prod.fst output present
    have mapped := congrArg (PMF.map Prod.snd) moved
    simpa only [PMF.map_comp, Function.comp_def] using mapped
  · have absent : output ∉ ((joint.map (fun pair => (pair.1, relabel pair.2))).map
        Prod.fst).support := by
      simpa only [PMF.map_comp, Function.comp_def] using present
    rw [fiberPosterior_of_not_mem_support _ _ present,
      fiberPosterior_of_not_mem_support _ _ absent]
    simp only [PMF.map_comp, Function.comp_def]

/-- Reindexing a private member family transports its complete actual
posterior, including the fallback at an impossible response. -/
theorem policyMixture_posterior_map {Other : Type}
    (prior : PMF Index) (relabel : Index → Other) (members : Other → app.Policy)
    (past : List app.PlayerEntry) :
    ((app.policyMixture prior (fun index => members (relabel index))).posterior past).map relabel =
      (app.policyMixture (prior.map relabel) members).posterior past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [Implementation.posterior_snoc, Implementation.posterior_snoc]
      let joint := ((app.policyMixture prior
        (fun index => members (relabel index))).posterior past).bind fun index =>
          (members (relabel index) past entry.beforeView).map (fun response => (response, index))
      have jointEq : joint.map (fun pair => (pair.1, relabel pair.2)) =
          ((app.policyMixture (prior.map relabel) members).posterior past).bind
            (fun index => (members index past entry.beforeView).map
              (fun response => (response, index))) := by
        rw [← ih]
        simp only [joint, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
      exact (posterior_map_memory joint relabel entry.action).trans
        (congrArg (fun law => (fiberPosterior law Prod.fst entry.action).map Prod.snd) jointEq)

/-- An unread coordinate of the original finite private plan retains its
weight law independently of the complete posterior on all other coordinates. -/
theorem policyMixture_posterior_coordinate {Pool : Type} [Fintype Pool] [DecidableEq Pool]
    {Part : Pool → Type} (weights : (pool : Pool) → PMF (Part pool))
    (members : ((pool : Pool) → Part pool) → app.Policy) (selected : Pool)
    (past : List app.PlayerEntry)
    (unread : ∀ (before : List app.PlayerEntry) (entry : app.PlayerEntry),
      before ++ [entry] <+: past → ∀ plan part,
        members (Function.update plan selected part) before entry.beforeView =
          members plan before entry.beforeView) :
    ∃ remainder : PMF ((pool : {pool // pool ≠ selected}) → Part pool.val),
      ((app.policyMixture (independentProduct weights) members).posterior past).map
          (Equiv.piSplitAt selected Part) =
        (weights selected).bind (fun part => remainder.map (Prod.mk part)) := by
  classical
  let split := Equiv.piSplitAt selected Part
  let restLaw := independentProduct (fun pool : {pool // pool ≠ selected} => weights pool.val)
  let pairMembers := fun pair : Part selected × ((pool : {pool // pool ≠ selected}) →
    Part pool.val) => members (split.symm pair)
  let reference := (weights selected).support_nonempty.choose
  let restMembers := fun rest => members (split.symm (reference, rest))
  have splitLaw : (independentProduct weights).map split =
      (weights selected).bind (fun part => restLaw.map (Prod.mk part)) := by
    rw [independentProduct_splitAt weights selected, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, split, Equiv.apply_symm_apply]
    rfl
  have transported := (app).policyMixture_posterior_map (independentProduct weights) split
    pairMembers past
  have same : (fun plan => pairMembers (split plan)) = members := by
    funext plan
    simp only [pairMembers, Equiv.symm_apply_apply]
  rw [same, splitLaw] at transported
  have product := (app).policyMixture_posterior_independent_left (weights selected) restLaw
    pairMembers restMembers past (fun before entry earlier part rest => by
      have updated : split.symm (part, rest) =
          Function.update (split.symm (reference, rest)) selected part := by
        funext pool
        by_cases equal : pool = selected
        · subst pool
          simp [split, Equiv.piSplitAt]
        · simp [split, Equiv.piSplitAt, equal]
      change members (split.symm (part, rest)) before entry.beforeView =
        members (split.symm (reference, rest)) before entry.beforeView
      rw [updated]
      exact unread before entry earlier _ part)
  exact ⟨(app.policyMixture restLaw restMembers).posterior past, transported.trans product⟩

end Interaction.ReactiveApplication
