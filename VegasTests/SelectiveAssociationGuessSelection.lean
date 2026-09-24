/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningSelection
import VegasTests.SelectiveAssociationCorrection

/-! # Bob's binding result is determined by his response information

At the final binding visit Bob has made exactly one earlier response. Thus
replays cannot introduce two competing older Bob binding envelopes. The full
raw response menu remains available.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

private theorem unique_of_length_le_one {α : Type} (entries : List α)
    (bound : entries.length ≤ 1) {first second : α}
    (firstMem : first ∈ entries) (secondMem : second ∈ entries) : first = second := by
  cases entries with
  | nil => simp at firstMem
  | cons head rest =>
      have empty : rest = [] := by
        have zero : rest.length = 0 := by simp only [List.length_cons] at bound; omega
        exact List.length_eq_zero_iff.mp zero
      subst rest
      exact (List.mem_singleton.mp firstMem).trans (List.mem_singleton.mp secondMem).symm

theorem native_bob_old_binding_unique (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobBinding) :
    nativeRuntime.UniqueEventOutput nativeLeaks bob bobBinding (control.execution.recall bob) := by
  intro first firstMem second secondMem _ _ _ _
  exact unique_of_length_le_one _ ((List.length_filterMap_le _ _).trans
    (Nat.le_of_eq (native_bob_binding_recall control trace active granted))) firstMem secondMem

/-- Every fixed raw response has the same resulting owned binding throughout
Bob's information set, despite arbitrary earlier submissions and replay. -/
theorem native_bob_binding_reserved_local (left right : nativeApp.Control)
    (leftTrace : nativeArena.Trace (some left)) (rightTrace : nativeArena.Trace (some right))
    (leftActive : left.actor = some bob) (rightActive : right.actor = some bob)
    (sameInput : (left.execution.recall bob, left.execution.observe nativeApp bob) =
      (right.execution.recall bob, right.execution.observe nativeApp bob))
    (granted : left.execution.application.serviceGrant = some bobBinding)
    (response : nativeApp.Action) (players : Player → nativeApp.Policy)
    (afterLeft afterRight : nativeApp.Execution)
    (leftMem : afterLeft ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobBinding bob) (left.execution.respond nativeApp bob response)).support)
    (rightMem : afterRight ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobBinding bob) (right.execution.respond nativeApp bob response)).support) :
    bobBindingRef.get? afterLeft.application.config.store =
      bobBindingRef.get? afterRight.application.config.store := by
  have recalls := congrArg Prod.fst sameInput
  have views := congrArg Prod.snd sameInput
  have applicationViews := congrArg ReactiveApplication.PlayerView.application views
  have ledgers := congrArg (fun view : nativeApp.PlayerView => view.messages.ledger) views
  have grants := congrArg (fun view : nativeApp.PlayerView =>
    view.application.publicView.serviceGrant) views
  have rightGrant : right.execution.application.serviceGrant = some bobBinding :=
    grants.symm.trans granted
  obtain ⟨leftOrigins, leftRecall, leftRetained, leftSerials, leftMemory, leftAudit⟩ :=
    native_transport_history left leftTrace bob leftActive
  obtain ⟨rightOrigins, rightRecall, rightRetained, rightSerials, rightMemory, rightAudit⟩ :=
    native_transport_history right rightTrace bob rightActive
  have ownerViews := nativeRuntime.reactive_playerView_congr nativeLeaks left.execution.application
    right.execution.application bob applicationViews (leftMemory.trans rightMemory.symm)
  have law := nativeRuntime.reactive_reserved_playerView_congr nativeLeaks bob bobBinding
    left.execution right.execution response ownerViews recalls ledgers
    leftOrigins rightOrigins leftRecall rightRecall leftRetained rightRetained
    (native_bob_old_binding_unique left leftTrace leftActive granted)
    (native_bob_old_binding_unique right rightTrace rightActive rightGrant)
    leftSerials rightSerials (leftAudit response) (rightAudit response)
  dsimp only at law
  rw [nativeRuntime.interaction_includeLatest_environment] at leftMem rightMem
  obtain ⟨next, pureStep⟩ := nativeRuntime.reactiveLatest_step_pure nativeLeaks bob bobBinding
    (left.execution.respond nativeApp bob response)
  rw [pureStep] at leftMem
  have firstEq := FinDist.mem_support_pure.mp leftMem
  subst afterLeft
  rw [pureStep, FinDist.map_pure] at law
  have mapped : afterRight.application.playerView bob ∈
      (FinDist.pure (next.application.playerView bob)).support := by
    rw [law, FinDist.support_map]
    exact ⟨afterRight, rightMem, rfl⟩
  have same := (FinDist.mem_support_pure.mp mapped).symm
  have binding := congrArg (fun view : PlayerView nativeGraph =>
    bobBindingRef.get? view.observation.store) same
  change bobBindingRef.get? (nativeGraph.playerStore bob next.application.config.store) =
    bobBindingRef.get? (nativeGraph.playerStore bob afterRight.application.config.store) at binding
  rwa [bobBindingRef.get?_playerStore bob _ rfl, bobBindingRef.get?_playerStore bob _ rfl]
    at binding

end VegasTests.SelectiveAssociation
