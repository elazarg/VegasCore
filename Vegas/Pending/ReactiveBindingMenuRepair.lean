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

/-- A copied canonical binding admitted by the compiled menu has
usable material, so its complete candidate-memory update equals defaulting.
The actual membership rules out an admitted missing or mistyped opening. -/
theorem copyResponse_binding_eq_of_compiled
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
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (opening : Option (Raw L))
    (originalFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh)
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩ :
      (runtime.reactiveApplication leaks).Action) ∈
        bounds.compiledActions runtime leaks who past view) :
    memory.copyResponse runtime leaks who view
        ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩ =
      memory.repairResponse runtime leaks who view
        ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩ := by
  have actualFresh := reactiveFreshSlot_spec view.application serial fresh
  rcases bounds.ordinary_binding_cases runtime leaks who past view event payload outputEq codeEq
      node turn owned ready serial fresh _ member with silent | ⟨value, _, _, same⟩
  · have impossible := (runtime.reactiveApplication leaks).silentPolicy_cases _ _ _ silent
    cases impossible
  · rw [runtime.reactiveBinding_normal_of_fresh leaks who past view event payload
      (.success value) serial actualFresh] at same
    have openingEq := congrArg (fun response : (runtime.reactiveApplication leaks).Action =>
      response.transmission.bind fun material => material.call.opening) same
    change opening = some (⟨payload, value⟩ : Raw L) at openingEq
    apply memory.copyResponse_usable_eq_repairResponse runtime leaks who view event payload
      outputEq codeEq node serial opening originalFresh actualFresh value
    rw [openingEq]
    exact Raw.as?_mk payload value

end Vegas.EventGraphRuntime.BindingMemory
