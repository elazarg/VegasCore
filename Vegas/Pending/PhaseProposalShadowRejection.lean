/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowOpeningAcceptance
import Vegas.Pending.EventBindingPublicObservation

/-! # Rejected original packets remain rejected under actual binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Binding admission is public even when its private result is unusable.
The actual phase token, excluded-owner and deadline gates are retained. -/
theorem PhaseStateFrame.binding_handler_isSome_eq {memory : BindingShadow graph}
    {owner : Player} {left right : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory owner left right)
    (owned : memory.OwnBindings owner) (runtime : EventGraphRuntime graph)
    (message : Message Player (CommitAttemptPacket graph))
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate) :
    (left.handle runtime message).isSome = (right.handle runtime message).isSome := by
  have publicEq : left.current.native.publicView = right.current.native.publicView := by
    rw [frame.current]
    exact native_publicView owned _
  have status := congrArg Option.isSome (handle_commitment_publicView_congr runtime
    left.current.native right.current.native publicEq message.id event candidate)
  simp only [Option.isSome_map] at status
  have attempts : left.attempt = right.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have allows : left.allows message.payload.packet.call =
      right.allows message.payload.packet.call := by
    simp only [PhaseRuntimeState.allows, frame.phases]
  have excluded : left.current.excludedCall message.payload.packet.call =
      right.current.excludedCall message.payload.packet.call := by rw [frame.current]; rfl
  unfold PhaseRuntimeState.handle
  rw [attempts, allows, excluded]
  split
  · simpa only [Option.isSome_map, call] using status
  · rfl

variable [Fintype Player] (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every rejected original counted packet has an actual rejected image.
The opening case uses genuine original certificate provenance, so a repaired
private failure cannot manufacture a new accepted plaintext. No cleared
attempt, empty archive or assumed target rejection is used. -/
theorem PhaseStateFrame.rejection_of_counted
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (left : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some left))
    {memory : BindingShadow graph} {owner : Player} {right : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory owner left.execution.application right)
    (owned : memory.OwnBindings owner)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ left.execution.network.inputs)
    (rejected : left.execution.application.handle runtime message = none) :
    right.handle runtime message = none := by
  cases call : message.payload.packet.call with
  | malformed raw =>
      unfold PhaseRuntimeState.handle
      split <;> simp only [call, handle, Option.map_none]
  | commitment event candidate =>
      have status := frame.binding_handler_isSome_eq owned runtime message event candidate call
      rw [rejected] at status
      cases accepted : right.handle runtime message with
      | none => rfl
      | some next =>
          simp only [accepted, Option.isSome_none, Option.isSome_some] at status
          cases status
  | opening event candidate raw =>
      cases accepted : right.handle runtime message with
      | none => rfl
      | some next =>
          obtain ⟨image, originalAccepted⟩ := frame.opening_acceptance_reflects runtime leaks
            bounds plan inputs horizon scheduler left trace owned message member event candidate raw
              call next accepted
          rw [rejected] at originalAccepted
          cases originalAccepted

end Vegas.EventGraphRuntime.BindingShadow
