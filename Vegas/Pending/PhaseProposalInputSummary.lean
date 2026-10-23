/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountServiceReference
import Vegas.Pending.PhaseOpeningPolicy

/-! # Counted encoders depend on emitted traffic and the current view

The exact raw menus and encoders retain their current catalogue and known
signed packets. Earlier inert private response syntax is absent from their
definitions once emitted outputs and the submission serial agree.
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

/-- Actual count menus retain complete signed packets and the current
catalogue, while ignoring old private syntax with the same emitted traffic. -/
theorem onePacketActions_congr_input (who : Player)
    (first second : List (app).PlayerEntry) (view : (app).PlayerView)
    (outputs : (app).outputs first = (app).outputs second)
    (serial : (app).submissionCount first = (app).submissionCount second) :
    onePacketActions runtime leaks bounds who first view =
      onePacketActions runtime leaks bounds who second view := by
  classical
  simp only [onePacketActions, rawMenu, OnePacketResponse, localEnvelope,
    ReactiveApplication.ResponseMenu.fromSubmissions,
    ReactiveApplication.ResponseMenu.knownPackets, outputs, serial]

private theorem bindingSlots_congr_input (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (first second : List (app).PlayerEntry) (view : (app).PlayerView)
    (outputs : (app).outputs first = (app).outputs second)
    (serial : (app).submissionCount first = (app).submissionCount second) :
    phaseBindingSlots runtime leaks bounds owner event payload first view =
      phaseBindingSlots runtime leaks bounds owner event payload second view := by
  unfold phaseBindingSlots
  rw [onePacketActions_congr_input runtime leaks bounds owner first second view outputs serial]

/-- The universal slot legality test and canonical allocator use the same
literal menu at equal traffic summaries. Only the current result law remains. -/
theorem bindingResultEncoder_congr_input (owner : Player) (event : graph.EventId)
    (payload : L.Ty)
    (results : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (first second : List (app).PlayerEntry) (view : (app).PlayerView)
    (outputs : (app).outputs first = (app).outputs second)
    (serial : (app).submissionCount first = (app).submissionCount second)
    (draw : results first view = results second view) :
    bindingResultEncoder runtime leaks bounds owner event payload results weight nonnegative
        atMostOne first view =
      bindingResultEncoder runtime leaks bounds owner event payload results weight nonnegative
        atMostOne second view := by
  classical
  have menuEq := onePacketActions_congr_input runtime leaks bounds owner first second view
    outputs serial
  have slotsEq := bindingSlots_congr_input runtime leaks bounds owner event payload first second
    view outputs serial
  have randomSlot : phaseBindingSlotPolicy runtime leaks bounds owner event payload results
      first view = phaseBindingSlotPolicy runtime leaks bounds owner event payload results
        second view := by
    unfold phaseBindingSlotPolicy
    rw [slotsEq, draw]
  have canonical : phaseBindingPolicy runtime leaks bounds owner event payload results first view =
      phaseBindingPolicy runtime leaks bounds owner event payload results second view := by
    unfold phaseBindingPolicy
    rw [menuEq, draw]
  unfold bindingResultEncoder
  rw [randomSlot, canonical]

/-- Truthful opening encoders depend on locked values, accepted handles and
the exact menu; inert old private aliases cannot change their lottery. -/
theorem phaseOpeningPolicy_congr_input (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (opens : List (app).PlayerEntry → (app).PlayerView → PMF Bool)
    (first second : List (app).PlayerEntry) (view : (app).PlayerView)
    (outputs : (app).outputs first = (app).outputs second)
    (serial : (app).submissionCount first = (app).submissionCount second)
    (draw : opens first view = opens second view) :
    phaseOpeningPolicy runtime leaks bounds owner event payload binding opens first view =
      phaseOpeningPolicy runtime leaks bounds owner event payload binding opens second view := by
  classical
  unfold phaseOpeningPolicy
  rw [onePacketActions_congr_input runtime leaks bounds owner first second view outputs serial,
    draw]

end Vegas.EventGraphRuntime.PhaseCount
