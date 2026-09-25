/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationCorrection
import VegasTests.SelectiveAssociationOpeningSelection

/-! # The binding result of a response is information-local

At every binding visit the owner has made at most one earlier response.
Consequently its current raw response, complete recall and observation determine
its reserved-inclusion binding result, even after arbitrary earlier play.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

theorem native_old_binding_unique (who : Player) (control : (serviceApp observation).Control)
    (trace : (serviceArena observation).Trace (some control)) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who)) :
    nativeRuntime.UniqueEventOutput observation who (nativeBindingEvent who)
      (control.execution.recall who) := by
  have count := native_decision_recall_count (observation := observation) (nativeBindingEvent who)
    control trace who active granted who
  have bounded : (control.execution.recall who).length ≤ 1 := by
    rw [count]
    fin_cases who <;> decide
  have length : ((serviceApp observation).outputs (control.execution.recall who)).length ≤ 1 :=
    (List.length_filterMap_le _ _).trans bounded
  intro first firstMem second secondMem _ _ _ _
  change first ∈ (serviceApp observation).outputs (control.execution.recall who) at firstMem
  change second ∈ (serviceApp observation).outputs (control.execution.recall who) at secondMem
  generalize (serviceApp observation).outputs (control.execution.recall who) = entries
    at length firstMem secondMem
  cases entries with
  | nil => simp at firstMem
  | cons head rest =>
      have empty : rest = [] := by
        have zero : rest.length = 0 := by simp only [List.length_cons] at length; omega
        exact List.length_eq_zero_iff.mp zero
      subst rest
      exact (List.mem_singleton.mp firstMem).trans (List.mem_singleton.mp secondMem).symm

/-- The actual inclusion result depends only on the binding owner's input
and current raw response, throughout its entire legal information set. -/
theorem native_binding_reserved_local (who : Player) (left right : (serviceApp observation).Control)
    (leftTrace : (serviceArena observation).Trace (some left)) (rightTrace : (serviceArena
      observation).Trace (some right))
    (leftActive : left.actor = some who) (rightActive : right.actor = some who)
    (sameInput : (left.execution.recall who, left.execution.observe (serviceApp observation) who) =
      (right.execution.recall who, right.execution.observe (serviceApp observation) who))
    (granted : left.execution.application.serviceGrant = some (nativeBindingEvent who))
    (response : (serviceApp observation).Action) (players : Player → (serviceApp
      observation).Policy)
    (afterLeft afterRight : (serviceApp observation).Execution)
    (leftMem : afterLeft ∈ (nativeRuntime.interactionStep observation players (serviceNetwork
      observation)
      (.includeLatest (nativeBindingEvent who) who) (left.execution.respond (serviceApp
        observation) who response)).support)
    (rightMem : afterRight ∈ (nativeRuntime.interactionStep observation players (serviceNetwork
      observation)
      (.includeLatest (nativeBindingEvent who) who) (right.execution.respond (serviceApp
        observation) who response)).support) :
    (nativeBindingRef who).get? afterLeft.application.config.store =
      (nativeBindingRef who).get? afterRight.application.config.store := by
  have recalls := congrArg Prod.fst sameInput
  have views := congrArg Prod.snd sameInput
  have applicationViews := congrArg ReactiveApplication.PlayerView.application views
  have ledgers := congrArg (fun view : (serviceApp observation).PlayerView =>
    view.messages.ledger) views
  have grants := congrArg (fun view : (serviceApp observation).PlayerView =>
    view.application.publicView.serviceGrant) views
  have rightGrant : right.execution.application.serviceGrant = some (nativeBindingEvent who) :=
    grants.symm.trans granted
  obtain ⟨leftOrigins, leftRecall, leftRetained, leftSerials, leftMemory, leftAudit⟩ :=
    native_transport_history left leftTrace who leftActive
  obtain ⟨rightOrigins, rightRecall, rightRetained, rightSerials, rightMemory, rightAudit⟩ :=
    native_transport_history right rightTrace who rightActive
  have ownerViews := nativeRuntime.reactive_playerView_congr observation left.execution.application
    right.execution.application who applicationViews (leftMemory.trans rightMemory.symm)
  have law := nativeRuntime.reactive_reserved_playerView_congr observation who
    (nativeBindingEvent who)
    left.execution right.execution response ownerViews recalls ledgers
    leftOrigins rightOrigins leftRecall rightRecall leftRetained rightRetained
    (native_old_binding_unique who left leftTrace leftActive granted)
    (native_old_binding_unique who right rightTrace rightActive rightGrant)
    leftSerials rightSerials (leftAudit response) (rightAudit response)
  dsimp only at law
  rw [nativeRuntime.interaction_includeLatest_environment] at leftMem rightMem
  obtain ⟨next, pureStep⟩ := nativeRuntime.reactiveLatest_step_pure observation who
    (nativeBindingEvent who)
    (left.execution.respond (serviceApp observation) who response)
  rw [pureStep] at leftMem
  have firstEq := FinDist.mem_support_pure.mp leftMem
  subst afterLeft
  rw [pureStep, FinDist.map_pure] at law
  have mapped : afterRight.application.playerView who ∈
      (FinDist.pure (next.application.playerView who)).support := by
    rw [law, FinDist.support_map]
    exact ⟨afterRight, rightMem, rfl⟩
  have same := (FinDist.mem_support_pure.mp mapped).symm
  have binding := congrArg (fun view : PlayerView nativeGraph =>
    (nativeBindingRef who).get? view.observation.store) same
  change (nativeBindingRef who).get? (nativeGraph.playerStore who next.application.config.store) =
    (nativeBindingRef who).get?
      (nativeGraph.playerStore who afterRight.application.config.store) at binding
  rwa [(nativeBindingRef who).get?_playerStore who _ rfl,
    (nativeBindingRef who).get?_playerStore who _ rfl] at binding

end VegasTests.SelectiveAssociation
