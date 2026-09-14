/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedReadOrigin
import Vegas.Compile.SealedResolvedStore
import Interaction.SealedResolutionEvents

/-! # Declared graph reads after nullable resolution

Completed public reveals supply public values, including timeout defaults.
Completed own commitments supply their registered value or the configured
null value. These facts make the declared reads of ready commitments available
without reconstructing a post-timeout source configuration.
-/

noncomputable section

namespace Vegas.EventGraph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

private theorem getAs_set_available (store : Store L) (field target : Nat)
    (ty : L.Ty) (value : L.Val ty) (havailable : (Store.getAs store field ty).isSome) :
    (Store.getAs (store.set target ⟨ty, value⟩) field ty).isSome := by
  by_cases heq : field = target
  · subst field
    simp [Store.getAs, TypedValue.as?]
  · rw [Store.getAs_set_ne store heq]
    exact havailable

private theorem Graph.replaySealedView_available (G : Graph Player L)
    (ty : L.Ty) (who : Player) (memory : Nat → Option (L.Val ty))
    (store : Store L) (events : List (SealedProgram.Event Player (L.Val ty)))
    (field : Nat) (havailable : (Store.getAs store field ty).isSome) :
    (Store.getAs (G.replaySealedView ty who memory store events) field ty).isSome := by
  induction events generalizing store with
  | nil => exact havailable
  | cons event rest ih =>
      dsimp only [Graph.replaySealedView]
      apply ih
      split
      · exact havailable
      · exact getAs_set_available store field _ ty _ havailable

private theorem Graph.replaySealedView_available_of_event (G : Graph Player L)
    (ty : L.Ty) (who : Player) (memory : Nat → Option (L.Val ty))
    (store : Store L) (events : List (SealedProgram.Event Player (L.Val ty)))
    (target : SealedProgram.Event Player (L.Val ty)) (value : L.Val ty)
    (hvalue : (match target with
      | .accepted _ handle => if handle.1 = who then memory handle.2 else none
      | .opened _ opened => some opened) = some value)
    (hmem : target ∈ events) :
    (Store.getAs (G.replaySealedView ty who memory store events)
      (G.nodeTarget target.node) ty).isSome := by
  induction events generalizing store with
  | nil => simp at hmem
  | cons event rest ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · dsimp only [Graph.replaySealedView]
        apply G.replaySealedView_available
        cases target <;> simp_all [Store.getAs, TypedValue.as?]
      · dsimp only [Graph.replaySealedView]
        exact ih _ htail

private theorem Graph.replaySealedView_getAs_initial (G : Graph Player L)
    (ty : L.Ty) (who : Player) (memory : Nat → Option (L.Val ty))
    (store : Store L) (events : List (SealedProgram.Event Player (L.Val ty)))
    (field : Nat) (fieldTy : L.Ty) (hfield : ∀ node, field ≠ G.nodeTarget node) :
    Store.getAs (G.replaySealedView ty who memory store events) field fieldTy =
      Store.getAs store field fieldTy := by
  induction events generalizing store with
  | nil => rfl
  | cons event rest ih =>
      dsimp only [Graph.replaySealedView]
      rw [ih]
      split
      · rfl
      · exact Store.getAs_set_ne store (hfield event.node) _ fieldTy

namespace SealedFragment

variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- The generated owner's accepted commitments retain their canonical handles
and locally cached values. This is a player-local observation invariant: it
places no condition on another owner's commitments or private service table. -/
def OwnCommitCache (supported : SealedFragment G ty) (who : Player)
    (events : List (SealedProgram.Event Player (L.Val ty)))
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry) :
    Prop :=
  ∀ (node : Fin G.nodeCount) (guard : EventGuard L),
    (G.nodeRow node).sem = .commit who guard →
    SealedProgram.done events node.val = true →
    ∃ value, SealedProgram.accepted? events node.val = some (who, node.val) ∧
      (supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = some value

/-- Registered-host invariants supply the player's local accepted-value cache. -/
theorem ownCommitCache_of_registered (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hinvariant : SealedResolution.EventInvariant (supported.resolvingRuntime nullValue window)
      execution.native.application)
    (hmemory : SealedResolution.RegistrationMemory (supported.resolvingRuntime nullValue window)
      execution) :
    supported.OwnCommitCache who execution.native.application.visible.events
      ((supported.resolvingRuntime nullValue window).eventHistory
        (execution.principalHistory who)) := by
  let runtime := supported.resolvingRuntime nullValue window
  intro node guard hsem hdone
  have hrule : runtime.program.rules[node.val]? =
      some ⟨.commit who, G.messagePrerequisites node⟩ := by
    change supported.compile.rules[node.val]? = _
    rw [supported.compile_rule, G.sealedRule_commit_eq node who guard hsem]
  have haccepted := hinvariant.accepted_of_done_commit node.val who
    (G.messagePrerequisites node) hrule hdone
  obtain ⟨_, value, _, _, _, _, hlookup⟩ :=
    hinvariant.acceptedBinding.accepted node.val (who, node.val) haccepted
  exact ⟨value, hinvariant.accepted?_eq_some_of_done_commit node.val who
    (G.messagePrerequisites node) hrule hdone,
    (runtime.eventHistory_cache (runtime.program.registrationEncoding node.val)
      (execution.principalHistory who)).trans ((hmemory who node.val).symm.trans hlookup)⟩

/-- Every declared read of a ready commitment is available in the actual
player-side store, including after other commitments or reveals have defaulted.
Only public event provenance, the owner's accepted-value cache, and prerequisite
completion are needed. Other owners' private service entries are unrestricted. -/
theorem resolvedPlayerStore_reads_of_ready (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (history : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (hpublic : SealedResolution.PublicEventInvariant (supported.resolvingRuntime nullValue window)
      view.application)
    (hcache : supported.OwnCommitCache who view.application.events
      ((supported.resolvingRuntime nullValue window).eventHistory history))
    (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (hrequires : (G.messagePrerequisites node).all
      view.application.completed = true) :
    ∃ reads, ReadEnv.ofStoreExec?
      (supported.resolvedPlayerStore who nullValue view.application.timeouts
        ((supported.resolvingRuntime nullValue window).eventHistory history)
        ((supported.resolvingRuntime nullValue window).eventView view)) guard.choiceReads =
      some reads := by
  let runtime := supported.resolvingRuntime nullValue window
  let localHistory := runtime.eventHistory history
  let localView := runtime.eventView view
  let memory := fun slot => (supported.compile.registrationEncoding slot).cachedValue
    (supported.compile.messageApplication (Value := L.Val ty)) localHistory
  change ∃ reads, ReadEnv.ofStoreExec?
    (supported.resolvedPlayerStore who nullValue view.application.timeouts
      localHistory localView) guard.choiceReads = some reads
  have havailable : ∀ ref, ref ∈ guard.choiceReads →
      (Store.getAs (supported.resolvedPlayerStore who nullValue
        view.application.timeouts localHistory localView) ref.field ref.ty).isSome := by
    intro ref href
    have horigin := supported.choiceRead_origin_of_prereqs_completed
      (fun prior => view.application.completed prior.val = true)
      node who guard hsem (fun prior hprior => List.all_eq_true.mp hrequires prior.val
        ((G.mem_messagePrerequisites node prior).mpr hprior)) ref href
    rcases horigin with ⟨spec, value, hfield, hsource, hty, howner⟩ |
        ⟨prior, htarget, hrefty, hcompleted, hproducer⟩
    · have hne := G.initial_field_ne_target ref.field spec value hfield hsource
      rw [supported.resolvedPlayerStore_getAs_of_not_owned_timeout_target who nullValue
        _ localHistory localView ref.field ref.ty (fun index _ _ _ => hne index)]
      change (Store.getAs (G.replaySealedView ty who memory (G.initialPlayerStore who)
        localView.application) ref.field ref.ty).isSome
      rw [G.replaySealedView_getAs_initial ty who memory _ _ ref.field ref.ty hne]
      simp [Store.getAs, Graph.initialPlayerStore, hfield, howner,
        FieldSpec.initialValue?, hsource, hty, TypedValue.as?]
    · rw [htarget, hrefty]
      rcases hproducer with ⟨priorGuard, hcommit⟩ | ⟨source, hreveal, _⟩
      · by_cases htimeout : prior.val ∈ view.application.timeouts
        · rw [supported.resolvedPlayerStore_getAs_timeout_commit who nullValue _
            localHistory localView prior priorGuard hcommit htimeout]
          rfl
        · have hdone : SealedProgram.done view.application.events
              prior.val = true := by
            simpa [SealedResolution.PublicState.completed, htimeout] using hcompleted
          obtain ⟨stored, haccepted, hstored⟩ := hcache prior priorGuard hcommit hdone
          have hacceptedMem := SealedProgram.accepted_mem_of_accepted?_eq_some haccepted
          apply supported.resolvedPlayerStore_available
          exact G.replaySealedView_available_of_event ty who memory _ _
            (.accepted prior.val (who, prior.val)) stored (by simpa using hstored) hacceptedMem
      · obtain ⟨producer, owner, producerGuard, hsource, hcommit⟩ :=
          supported.revealSource prior source hreveal
        have hrule : runtime.program.rules[prior.val]? =
            some ⟨.reveal owner producer.val, G.messagePrerequisites prior⟩ := by
          change supported.compile.rules[prior.val]? = _
          rw [supported.compile_rule]
          exact congrArg some (G.sealedRule_reveal_eq prior producer owner producerGuard
            (hsource ▸ hreveal) hcommit)
        obtain ⟨value, hopened⟩ := hpublic.opened_of_completed_reveal
          prior.val owner
          producer.val (G.messagePrerequisites prior) hrule hcompleted
        apply supported.resolvedPlayerStore_available
        exact G.replaySealedView_available_of_event ty who memory _ _
          (.opened prior.val value) value rfl hopened
  unfold ReadEnv.ofStoreExec?
  exact ⟨_, dif_pos havailable⟩

end SealedFragment

end Vegas.EventGraph

/-- info: 'Vegas.EventGraph.SealedFragment.resolvedPlayerStore_reads_of_ready' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.resolvedPlayerStore_reads_of_ready
