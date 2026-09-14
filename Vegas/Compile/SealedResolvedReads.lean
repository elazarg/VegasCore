/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedReadOrigin
import Vegas.Compile.SealedResolvedStore
import Interaction.SealedResolutionEvents

/-! # Declared source reads after nullable resolution

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

/-- Every declared read of a ready commitment is available in the actual
player-side store, including after other commitments or reveals have defaulted.
The hypotheses are native invariants and prerequisite completion, not a
post-timeout decoded source state or the desired progress conclusion. -/
theorem resolvedPlayerStore_reads_of_ready (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hinvariant : SealedResolution.EventInvariant (supported.resolvingRuntime nullValue window)
      execution.native.application)
    (hmemory : SealedResolution.RegistrationMemory (supported.resolvingRuntime nullValue window)
      execution)
    (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (hrequires : (G.messagePrerequisites node).all
      execution.native.application.visible.completed = true) :
    ∃ reads, ReadEnv.ofStoreExec?
      (supported.resolvedPlayerStore who nullValue execution.native.application.visible.timeouts
        ((supported.resolvingRuntime nullValue window).eventHistory
          (execution.principalHistory who))
        ((supported.resolvingRuntime nullValue window).eventView
          (MessageApplication.State.observe _ execution.native who))) guard.choiceReads =
      some reads := by
  let runtime := supported.resolvingRuntime nullValue window
  let history := runtime.eventHistory (execution.principalHistory who)
  let view := runtime.eventView (MessageApplication.State.observe _ execution.native who)
  let memory := fun slot => (supported.compile.registrationEncoding slot).cachedValue
    (supported.compile.messageApplication (Value := L.Val ty)) history
  have hcache (slot : Nat) :
      execution.native.application.service.lookup (who, slot) = memory slot :=
    (hmemory who slot).trans (runtime.eventHistory_cache
      (runtime.program.registrationEncoding slot) (execution.principalHistory who)).symm
  change ∃ reads, ReadEnv.ofStoreExec?
    (supported.resolvedPlayerStore who nullValue execution.native.application.visible.timeouts
      history view) guard.choiceReads = some reads
  have havailable : ∀ ref, ref ∈ guard.choiceReads →
      (Store.getAs (supported.resolvedPlayerStore who nullValue
        execution.native.application.visible.timeouts history view) ref.field ref.ty).isSome := by
    intro ref href
    have horigin := supported.choiceRead_origin_of_prereqs_completed
      (fun prior => execution.native.application.visible.completed prior.val = true)
      node who guard hsem (fun prior hprior => List.all_eq_true.mp hrequires prior.val
        ((G.mem_messagePrerequisites node prior).mpr hprior)) ref href
    rcases horigin with ⟨spec, value, hfield, hsource, hty, howner⟩ |
        ⟨prior, htarget, hrefty, hcompleted, hproducer⟩
    · have hne := G.initial_field_ne_target ref.field spec value hfield hsource
      rw [supported.resolvedPlayerStore_getAs_of_not_owned_timeout_target who nullValue
        _ history view ref.field ref.ty (fun index _ _ _ => hne index)]
      change (Store.getAs (G.replaySealedView ty who memory (G.initialPlayerStore who)
        view.application) ref.field ref.ty).isSome
      rw [G.replaySealedView_getAs_initial ty who memory _ _ ref.field ref.ty hne]
      simp [Store.getAs, Graph.initialPlayerStore, hfield, howner,
        FieldSpec.initialValue?, hsource, hty, TypedValue.as?]
    · rw [htarget, hrefty]
      rcases hproducer with ⟨priorGuard, hcommit⟩ | ⟨source, hreveal, _⟩
      · by_cases htimeout : prior.val ∈ execution.native.application.visible.timeouts
        · rw [supported.resolvedPlayerStore_getAs_timeout_commit who nullValue _ history view
            prior priorGuard hcommit htimeout]
          rfl
        · have hdone : SealedProgram.done execution.native.application.visible.events
              prior.val = true := by
            simpa [SealedResolution.PublicState.completed, htimeout] using hcompleted
          have hrule : runtime.program.rules[prior.val]? =
              some ⟨.commit who, G.messagePrerequisites prior⟩ := by
            change supported.compile.rules[prior.val]? = _
            rw [supported.compile_rule]
            exact congrArg some (G.sealedRule_commit_eq prior who priorGuard hcommit)
          have haccepted := hinvariant.accepted_of_done_commit prior.val who
            (G.messagePrerequisites prior) hrule hdone
          obtain ⟨_, stored, _, _, _, _, hlookup⟩ :=
            hinvariant.acceptedBinding.accepted prior.val (who, prior.val) haccepted
          have hstored : memory prior.val = some stored := (hcache prior.val).symm.trans hlookup
          apply supported.resolvedPlayerStore_available
          exact G.replaySealedView_available_of_event ty who memory _ _
            (.accepted prior.val (who, prior.val)) stored (by simpa using hstored) haccepted
      · obtain ⟨producer, owner, producerGuard, hsource, hcommit⟩ :=
          supported.revealSource prior source hreveal
        have hrule : runtime.program.rules[prior.val]? =
            some ⟨.reveal owner producer.val, G.messagePrerequisites prior⟩ := by
          change supported.compile.rules[prior.val]? = _
          rw [supported.compile_rule]
          exact congrArg some (G.sealedRule_reveal_eq prior producer owner producerGuard
            (hsource ▸ hreveal) hcommit)
        obtain ⟨value, hopened⟩ := hinvariant.opened_of_completed_reveal prior.val owner
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
