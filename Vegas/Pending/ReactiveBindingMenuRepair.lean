/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingContinuation

/-! # Every clean binding repair is an actual retained response

Usable bounded material is retained unchanged. Missing or mistyped material is
replaced by an admitted default value. The local fallback of the total private
implementation is therefore absent on the whole canonical binding branch.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph)

/-- The complete canonical branch, rather than just the unusable subcase,
has a legal repaired response at the same current own input. -/
theorem repairResponse_binding_available
    (who : Player) (memory : BindingMemory runtime leaks)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.OwnTurn who event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (opening : Option (Raw L)) (bounded : bounds.AllowsOpening opening)
    (originalFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh) :
    (memory.repairResponse runtime leaks who view
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩).1 ∈
        bounds.requiredDecisionActions runtime leaks who past view := by
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  cases decoded : opening.bind (fun raw => raw.as? payload) with
  | none =>
      exact repairResponse_required runtime leaks bounds who memory past view event payload
        outputEq codeEq node turn owned ready unsent serial fresh capacity default opening
          originalFresh decoded
  | some value =>
      rw [congrArg Prod.fst (memory.repairResponse_usable runtime leaks who view event payload
        outputEq codeEq node serial opening originalFresh
          (reactiveFreshSlot_spec view.application serial fresh) value decoded)]
      have cases := bounds.canonical_binding_response_cases runtime leaks who past view event
        payload outputEq codeEq node turn owned ready unsent serial fresh capacity
        opening bounded
      rcases cases with available | impossible
      · exact available
      · rw [decoded] at impossible
        cases impossible

/-- At a clean required opportunity, the legal private implementation equals
its original repair kernel for every mixed canonical bounded response law. -/
theorem retainedImplementation_binding_response
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (who : Player) (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (memory : BindingMemory runtime leaks)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.OwnTurn who event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (originalFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh)
    (coverage : bounds.requiredDecisionActions runtime leaks who past view ⊆
      menu.actions who past view)
    (canonical : ∀ response ∈ (policy (memory.restoreRecall runtime leaks past)
      (memory.shadow.inputView runtime leaks view)).support,
      ∃ opening, bounds.AllowsOpening opening ∧ response =
        ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩) :
    (retainedImplementation runtime leaks menu who reference policy).respond memory (past, view) =
      (implementation runtime leaks who reference policy).respond memory (past, view) := by
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  apply retainedImplementation_respond_eq
  intro result supported
  change result ∈ ((policy (memory.restoreRecall runtime leaks past)
    (memory.shadow.inputView runtime leaks view)).map _).support at supported
  obtain ⟨response, selected, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨opening, bounded, rfl⟩ := canonical response selected
  apply coverage
  exact repairResponse_binding_available runtime leaks bounds who memory past view event payload
    outputEq codeEq node turn owned ready unsent serial fresh capacity default opening bounded
    originalFresh

end Vegas.EventGraphRuntime.BindingMemory
