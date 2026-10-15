/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingPolicy

/-! # Source-value-preserving fresh-slot laws for phased bindings -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

open Classical in
/-- Every bounded fresh slot whose complete typed-result encoding is legal.
The test uses only the actual owner's private view and recalled responses. -/
def phaseBindingSlots (who : Player) (event : graph.EventId) (payload : L.Ty)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) : Finset Nat :=
  (Finset.range bounds.candidateCount).filter fun serial =>
    view.application.1.candidates (.prepared serial) = .fresh ∧
      ∀ result, phaseBindingResponse runtime leaks who event payload result serial ∈
        onePacketActions runtime leaks bounds who past view

open Classical in
/-- Draw the physical slot independently of the original typed-result law.
At inputs without an eligible slot the globally legal response is silence. -/
def phaseBindingSlotPolicy (who : Player) (event : graph.EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload))) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  if nonempty : (phaseBindingSlots runtime leaks bounds who event payload past view).Nonempty then
    (PMF.uniformOfFinset _ nonempty).bind fun serial =>
      (results past view).map (phaseBindingResponse runtime leaks who event payload · serial)
  else PMF.pure ⟨none⟩

/-- Every supported response respects the actual one-packet menu, including at
inputs outside every initialized execution. -/
theorem phaseBindingSlotPolicy_covered (who : Player) (event : graph.EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈
      (phaseBindingSlotPolicy runtime leaks bounds who event payload results past view).support) :
    response ∈ onePacketActions runtime leaks bounds who past view := by
  classical
  unfold phaseBindingSlotPolicy at supported
  split at supported
  · obtain ⟨serial, selected, drawn⟩ := (PMF.mem_support_bind_iff ..).mp supported
    have eligible := (PMF.mem_support_uniformOfFinset_iff ..).mp selected
    obtain ⟨result, _drawn, rfl⟩ := (PMF.mem_support_map_iff ..).mp drawn
    exact (Finset.mem_filter.mp eligible).2.2 result
  · cases (PMF.mem_support_pure_iff ..).mp supported
    exact silence_onePacket runtime leaks bounds who past view

/-- The slot tier dominates every encoded typed result at every eligible slot
by its original mass divided by the number of eligible slots. -/
theorem phaseBindingSlotPolicy_mass (who : Player) (event : graph.EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (serial : Nat)
    (eligible : serial ∈ phaseBindingSlots runtime leaks bounds who event payload past view)
    (result : PublicationResult (L.Val payload)) :
    ((phaseBindingSlots runtime leaks bounds who event payload past view).card : ENNReal)⁻¹ *
        results past view result ≤
      phaseBindingSlotPolicy runtime leaks bounds who event payload results past view
        (phaseBindingResponse runtime leaks who event payload result serial) := by
  classical
  have nonempty : (phaseBindingSlots runtime leaks bounds who event payload past view).Nonempty :=
    ⟨serial, eligible⟩
  rw [phaseBindingSlotPolicy, dite_eq_left nonempty, PMF.bind_apply]
  have lower : results past view result ≤
      ((results past view).map
        (phaseBindingResponse runtime leaks who event payload · serial))
          (phaseBindingResponse runtime leaks who event payload result serial) := by
    rw [PMF.map_apply]
    simpa only [ite_eq_left rfl, ite_true] using (ENNReal.le_tsum
      (f := fun value => if phaseBindingResponse runtime leaks who event payload result serial =
          phaseBindingResponse runtime leaks who event payload value serial
        then results past view value else 0) result)
  calc
    _ ≤ PMF.uniformOfFinset _ nonempty serial *
        ((results past view).map
          (phaseBindingResponse runtime leaks who event payload · serial))
            (phaseBindingResponse runtime leaks who event payload result serial) := by
      rw [PMF.uniformOfFinset_apply_of_mem nonempty eligible]
      gcongr
    _ ≤ _ := ENNReal.le_tsum (f := fun slot =>
      PMF.uniformOfFinset _ nonempty slot *
        ((results past view).map
          (phaseBindingResponse runtime leaks who event payload · slot))
            (phaseBindingResponse runtime leaks who event payload result serial)) serial

/-- Sampling a fresh slot leaves the original typed-result law unchanged in
the actual persistent catalogue after the authored response. -/
theorem phaseBindingSlotPolicy_result_law
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (nonempty : (phaseBindingSlots runtime leaks bounds who event payload
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).Nonempty) :
    (phaseBindingSlotPolicy runtime leaks bounds who event payload results
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).map
      (fun response =>
        let serial := (PhaseCandidates.responseCandidateSlot runtime leaks response).getD 0
        let next := execution.respond (phaseApplication runtime leaks) who response
        next.application.current.native.bindingResult (who, .prepared serial) payload) =
      results (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) := by
  classical
  rw [phaseBindingSlotPolicy, dite_eq_left nonempty, PMF.map_bind]
  have inner (serial : Nat)
      (selected : serial ∈ (PMF.uniformOfFinset _ nonempty).support) :
      ((results (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who)).map
          (phaseBindingResponse runtime leaks who event payload · serial)).map
        (fun response =>
          let slot := (PhaseCandidates.responseCandidateSlot runtime leaks response).getD 0
          let next := execution.respond (phaseApplication runtime leaks) who response
          next.application.current.native.bindingResult (who, .prepared slot) payload) =
        results (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) := by
    have eligible := (PMF.mem_support_uniformOfFinset_iff ..).mp selected
    have fresh := (Finset.mem_filter.mp eligible).2.1
    rw [PMF.map_comp]
    have mapped : (fun result =>
        let response := phaseBindingResponse runtime leaks who event payload result serial
        let slot := (PhaseCandidates.responseCandidateSlot runtime leaks response).getD 0
        let next := execution.respond (phaseApplication runtime leaks) who response
        next.application.current.native.bindingResult (who, .prepared slot) payload) = id := by
      funext result
      change (execution.respond _ who _).application.current.native.bindingResult
        (who, .prepared serial) payload = result
      exact phaseBindingResponse_result runtime leaks execution who event payload result serial
        fresh
    exact (congrArg (fun f => (results (execution.recall who)
      (execution.observe (phaseApplication runtime leaks) who)).map f) mapped).trans (PMF.map_id _)
  calc
    _ = (PMF.uniformOfFinset _ nonempty).bind (fun _ => results
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)) :=
      bind_congr_on_support _ inner
    _ = _ := PMF.bind_const _ _

end Vegas.EventGraphRuntime.PhaseCount
