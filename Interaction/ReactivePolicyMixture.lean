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

end Interaction.ReactiveApplication
