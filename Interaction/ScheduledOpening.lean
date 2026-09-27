/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyMixture

/-! # A scheduled mixture stops after its first opening

An opening action disjoint from the waiting policy identifies the selected
slot in the player's own response recall. All later behavior uses the waiting
policy, including after other zero-probability recorded responses. This proves
the off-path stop rule for fully mixed scheduled approximants; it does not
identify a zero-weight mixture's fallback with their limit.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

theorem policyMixture_posterior_pure_snoc {Index : Type} (initial : FinDist Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (index : Index) (fixed : (app.policyMixture initial policies).posterior past =
      FinDist.pure index) :
    (app.policyMixture initial policies).posterior (past ++ [entry]) =
      FinDist.pure index := by
  rw [Implementation.posterior_snoc, fixed]
  change ((FinDist.pure index).bind (fun value =>
    (policies value past entry.beforeView).map fun action => (action, value))
      |>.condOnFibre Prod.fst entry.action).map Prod.snd = FinDist.pure index
  rw [FinDist.pure_bind]
  have paired : (policies index past entry.beforeView).map (fun action => (action, index)) =
      FinDist.product (policies index past entry.beforeView) (FinDist.pure index) := by
    simp only [FinDist.product, FinDist.map_eq_bind, FinDist.pure_bind]
  rw [paired, FinDist.conditional_snd_product]

theorem policyMixture_posterior_pure_append {Index : Type} (initial : FinDist Index)
    (policies : Index → app.Policy) (past suffix : List app.PlayerEntry) (index : Index)
    (fixed : (app.policyMixture initial policies).posterior past = FinDist.pure index) :
    (app.policyMixture initial policies).posterior (past ++ suffix) = FinDist.pure index := by
  induction suffix using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using fixed
  | append_singleton suffix entry ih =>
      rw [← List.append_assoc]
      exact app.policyMixture_posterior_pure_snoc initial policies _ entry index ih

/-- Observing a supported opening pins its scheduled slot exactly. -/
theorem scheduledMixture_posterior_open {slots : Nat}
    (initial : FinDist (Option (Fin slots))) (offset : Nat)
    (opening : app.Action) (waiting : app.Policy) (slot : Fin slots)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (atSlot : past.length = offset + slot.val) (opened : entry.action = opening)
    (distinct : opening ∉ (waiting past entry.beforeView).support)
    (supported : opening ∈
      ((app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
        (fun _ _ => FinDist.pure opening) waiting)).policy past entry.beforeView).support) :
    (app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure opening) waiting)).posterior (past ++ [entry]) =
        FinDist.pure (some slot) := by
  classical
  let policies := fun selected : Option (Fin slots) =>
    app.scheduledPolicy offset selected (fun _ _ => FinDist.pure opening) waiting
  let mixture := app.policyMixture initial policies
  let joint := (mixture.posterior past).bind fun index =>
    (policies index past entry.beforeView).map fun action => (action, index)
  have possible : ∃ response ∈ Prod.fst ⁻¹' {opening}, response ∈ joint.support := by
    change opening ∈ (joint.map Prod.fst).support at supported
    obtain ⟨response, member, first⟩ := FinDist.support_map .. ▸ supported
    exact ⟨response, first, member⟩
  change mixture.posterior (past ++ [entry]) = _
  rw [Implementation.posterior_snoc]
  change (joint.condOnFibre Prod.fst entry.action).map Prod.snd = _
  rw [opened, FinDist.condOnFibre, dite_eq_left possible]
  apply FinDist.eq_pure_of_support_subset_singleton
  intro selected member
  obtain ⟨response, conditional, second⟩ := FinDist.support_map .. ▸ member
  have facts := FinDist.support_condOn joint _ possible conditional
  have first : response.1 = opening := facts.1
  have original := facts.2
  simp only [joint, FinDist.support_bind, Set.mem_iUnion] at original
  obtain ⟨index, _, produced⟩ := original
  obtain ⟨action, actionSupport, pairEq⟩ := FinDist.support_map .. ▸ produced
  have actionEq : action = opening := (congrArg Prod.fst pairEq).trans first
  have indexEq : index = selected := (congrArg Prod.snd pairEq).trans second
  subst action
  subst index
  change opening ∈ (app.scheduledPolicy offset selected
    (fun _ _ => FinDist.pure opening) waiting past entry.beforeView).support at actionSupport
  unfold scheduledPolicy at actionSupport
  split at actionSupport
  · rename_i chosen
    cases selected with
    | none => simp at chosen
    | some selected =>
        have equal : selected = slot := by
          simp only [Option.map_some, Option.some.injEq, atSlot] at chosen
          apply Fin.ext
          omega
        exact Set.mem_singleton_iff.mpr (congrArg some equal)
  · exact (distinct actionSupport).elim

/-- All subsequent responses use the waiting policy. The entire recorded
suffix is permitted, so the statement also controls off-path continuations
after the first supported opening. -/
theorem scheduledMixture_after_open {slots : Nat}
    (initial : FinDist (Option (Fin slots))) (offset : Nat)
    (opening : app.Action) (waiting : app.Policy) (slot : Fin slots)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (atSlot : past.length = offset + slot.val) (opened : entry.action = opening)
    (distinct : opening ∉ (waiting past entry.beforeView).support)
    (supported : opening ∈
      ((app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
        (fun _ _ => FinDist.pure opening) waiting)).policy past entry.beforeView).support)
    (suffix : List app.PlayerEntry) (view : app.PlayerView) :
    let policies := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure opening) waiting
    (app.policyMixture initial policies).policy (past ++ [entry] ++ suffix) view =
      waiting (past ++ [entry] ++ suffix) view := by
  dsimp only
  have fixed := app.scheduledMixture_posterior_open initial offset opening waiting slot
    past entry atSlot opened distinct supported
  have retained := app.policyMixture_posterior_pure_append initial
    (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure opening) waiting) (past ++ [entry]) suffix (some slot) fixed
  rw [app.policyMixture_policy, retained, FinDist.pure_bind]
  unfold scheduledPolicy
  apply ite_eq_right
  simp only [Option.map_some, Option.some.injEq,
    List.length_append, List.length_singleton, atSlot]
  omega

end Interaction.ReactiveApplication
