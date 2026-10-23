/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingSlotHistory
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Normalized local binding service with a separate counted send tier -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- The original typed-result draw is followed by an independent fresh-slot draw.
The canonical allocator handles the complementary slot component. -/
def bindingResultEncoder (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    (app).Policy := fun past view =>
  mix slotWeight slotNonnegative slotBounded
    (phaseBindingSlotPolicy runtime leaks bounds owner event payload
      values past view)
    (phaseBindingPolicy runtime leaks bounds owner event payload
      values past view)

theorem bindingResultEncoder_covered (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (bindingResultEncoder runtime leaks bounds owner event payload values
      slotWeight slotNonnegative slotBounded past view).support) :
    response ∈ onePacketActions runtime leaks bounds owner past view := by
  rcases support_mix_subset _ _ _ _ _ supported with first | second
  · exact phaseBindingSlotPolicy_covered runtime leaks bounds owner event payload _ _ _ _ first
  · exact phaseBindingPolicy_covered runtime leaks bounds owner event payload _ _ _ _ second

end Vegas.EventGraphRuntime.PhaseCount
