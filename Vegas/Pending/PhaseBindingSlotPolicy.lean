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

end Vegas.EventGraphRuntime.PhaseCount
