/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhasePreparedOnePacket

/-! # Globally legal phased policies for one selected binding

The local typed-result law can depend on the complete actual private input.
The implementation uses its locally visible fresh slot and waits at inputs
where the requested encoding is outside the actual one-packet menu.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

open Classical in
/-- A selected-event binding component is globally menu-legal. Its guard is
inactive at every genuine unsent ready callback with sufficient wire capacity. -/
def phaseBindingPolicy (who : Player) (event : graph.EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload))) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  match reactiveFreshSlot view.application.1 with
  | none => PMF.pure ⟨none⟩
  | some serial =>
      if ∀ result, phaseBindingResponse runtime leaks who event payload result serial ∈
          onePacketActions runtime leaks bounds who past view then
        (results past view).map (phaseBindingResponse runtime leaks who event payload · serial)
      else PMF.pure ⟨none⟩

/-- The complete policy is legal at every local input, including inputs that
are not realized by an initialized physical execution. -/
theorem phaseBindingPolicy_covered (who : Player) (event : graph.EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈
      (phaseBindingPolicy runtime leaks bounds who event payload results past view).support) :
    response ∈ onePacketActions runtime leaks bounds who past view := by
  classical
  unfold phaseBindingPolicy at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact silence_onePacket runtime leaks bounds who past view
  · split at supported
    · rename_i serial _ covered
      obtain ⟨result, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact covered result
    · cases (PMF.mem_support_pure_iff _ _).mp supported
      exact silence_onePacket runtime leaks bounds who past view

/-- Every genuine unsent ready binding realizes its complete requested result
law in the permanent catalogue. The capacity, freshness and count guards are
proved from the actual history, including arbitrary prior attempts and traffic. -/
theorem phaseBindingPolicy_of_history
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (active : control.actor = some who)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ serial, serial < horizon ∧
      phaseBindingPolicy runtime leaks bounds who event payload results
          (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) =
        (results (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who)).map
            (phaseBindingResponse runtime leaks who event payload · serial) ∧
      (phaseBindingPolicy runtime leaks bounds who event payload results
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).map
          (fun response =>
            let next := control.execution.respond (phaseApplication runtime leaks) who response
            next.application.current.native.bindingResult (who, .prepared serial) payload) =
        results (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨serial, bounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    plan inputs horizon scheduler control raw who active
  have fresh := reactiveFreshSlot_spec _ serial selected
  have fixed := phaseOwnCommitmentsFixed_history runtime leaks initial horizon scheduler raw
  have recalled := countRecall_history runtime leaks raw
  have covered (result : PublicationResult (L.Val payload)) :
      phaseBindingResponse runtime leaks who event payload result serial ∈
        onePacketActions runtime leaks bounds who (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) := by
    rw [mem_onePacketActions]
    exact ⟨phaseBindingResponse_available runtime leaks bounds who _ _ event payload values
      result serial (bounded.trans_le capacity), Or.inr
        (phaseBindingResponse_permitted runtime leaks control.execution recalled fixed who event
          payload outputEq request unsent result serial fresh)⟩
  have law : phaseBindingPolicy runtime leaks bounds who event payload results
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who) =
      (results (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).map
          (phaseBindingResponse runtime leaks who event payload · serial) := by
    unfold phaseBindingPolicy
    simp only [selected, ite_eq_left covered]
  refine ⟨serial, bounded, law, ?_⟩
  rw [law]
  exact phaseBindingResponse_result_law runtime leaks control.execution who event payload _
    serial fresh

end Vegas.EventGraphRuntime.PhaseCount
