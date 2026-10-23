/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalResponseAliases
import Vegas.Pending.PhaseCountServiceReference

/-! # Packet marginals of private proposal encodings

The response class retains the complete emitted packet. Summing its actual
private aliases therefore preserves packet probabilities even when different
typed preparations have different numbers of private syntax representatives.
The binding encoder chooses its physical slot before its private typed result.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- The complete locally materialized packet of a binding at a fixed slot
does not depend on its hidden typed result, including preparation failure. -/
theorem phaseBindingResponse_localPacket (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    ((phaseBindingResponse runtime leaks owner event payload first serial).transmission.map
        fun material => (localEnvelope runtime leaks owner past view material).payload) =
      ((phaseBindingResponse runtime leaks owner event payload second serial).transmission.map
        fun material => (localEnvelope runtime leaks owner past view material).payload) := by
  rfl

omit [Fintype Player] in
/-- Holding a physical slot fixed, any private typed-result law has the same
packet marginal. This is a pointwise encoder statement at the full local input. -/
theorem phaseBindingResponse_packet_law (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (results : PMF (PublicationResult (L.Val payload))) (serial : Nat) :
    ((results.map (phaseBindingResponse runtime leaks owner event payload · serial)).map
        fun response => response.transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) =
      PMF.pure ((phaseBindingResponse runtime leaks owner event payload .failure
        serial).transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) := by
  rw [PMF.map_comp]
  calc
    _ = results.map (fun _ =>
        (phaseBindingResponse runtime leaks owner event payload .failure serial).transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) := by
      apply map_congr_on_support
      intro result _
      exact phaseBindingResponse_localPacket runtime leaks owner event payload past view
        result .failure serial
    _ = _ := PMF.map_const _ _

/-- The canonical allocator and its universal legality test do not inspect
the selected result law. This conclusion also covers forced-silence inputs. -/
theorem phaseBindingPolicy_packet_congr (owner : Player) (event : graph.EventId)
    (payload : L.Ty)
    (first second : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (phaseBindingPolicy runtime leaks bounds owner event payload first past view).map
        (fun response => response.transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) =
      (phaseBindingPolicy runtime leaks bounds owner event payload second past view).map
        (fun response => response.transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) := by
  classical
  unfold phaseBindingPolicy
  split
  · rfl
  · split
    · rw [phaseBindingResponse_packet_law, phaseBindingResponse_packet_law]
    · rfl

/-- The eligible-slot set tests every typed result, rather than the drawn
result. Thus summing its independent slot draw leaves a value-free packet law. -/
theorem phaseBindingSlotPolicy_packet_congr (owner : Player) (event : graph.EventId)
    (payload : L.Ty)
    (first second : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (phaseBindingSlotPolicy runtime leaks bounds owner event payload first past view).map
        (fun response => response.transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) =
      (phaseBindingSlotPolicy runtime leaks bounds owner event payload second past view).map
        (fun response => response.transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) := by
  classical
  unfold phaseBindingSlotPolicy
  split
  · rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support
    intro serial _
    rw [phaseBindingResponse_packet_law, phaseBindingResponse_packet_law]
  · rfl

/-- Actual canonical and randomized-slot branches have a common packet law
for every pair of private result laws at the same full local input. -/
theorem bindingResultEncoder_packet_congr (owner : Player) (event : graph.EventId)
    (payload : L.Ty)
    (first second : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (slotWeight : ℝ) (nonnegative : 0 ≤ slotWeight) (atMostOne : slotWeight ≤ 1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (bindingResultEncoder runtime leaks bounds owner event payload first slotWeight nonnegative
        atMostOne past view).map (fun response => response.transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) =
      (bindingResultEncoder runtime leaks bounds owner event payload second slotWeight nonnegative
        atMostOne past view).map (fun response => response.transmission.map
          (fun material => (localEnvelope runtime leaks owner past view material).payload)) := by
  unfold bindingResultEncoder
  rw [mix_map, mix_map,
    phaseBindingSlotPolicy_packet_congr runtime leaks bounds owner event payload first second,
    phaseBindingPolicy_packet_congr runtime leaks bounds owner event payload first second]

end Vegas.EventGraphRuntime.PhaseCount
