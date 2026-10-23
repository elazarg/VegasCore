/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventApplication

/-! # Native accepted events belong to their authenticated sender -/

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The native handler accepts only the source event owned by the packet sender.
This holds for arbitrary raw packets, without any prescribed-policy premise. -/
theorem handle_event_actor (runtime : EventGraphRuntime graph) (state after : State graph)
    (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some after) :
    ∃ event, message.payload.event? graph = some event ∧
      graph.actor? event = some message.sender := by
  cases packet : message.payload with
  | malformed raw => simp [handle, packet] at accepted
  | commitment event candidate =>
    refine ⟨event, rfl, ?_⟩
    by_cases ready : state.config.cut.Ready event
    · by_cases timely : state.WithinDeadline runtime event
      · cases node : nodeView graph event with
        | sample payload law outputEq codeEq =>
          simp [handle, packet, ready, timely, node] at accepted
        | resolve owner payload binding checks outputEq codeEq =>
          simp [handle, packet, ready, timely, node] at accepted
        | bind owner payload outputEq codeEq =>
          have sender : message.sender = owner := by
            by_contra different
            simp [handle, packet, ready, timely, node, different] at accepted
          rw [sender]
          change (graph.nodes event).actor = some owner
          rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
          rfl
      · simp [handle, packet, ready, timely] at accepted
    · simp [handle, packet, ready] at accepted
  | opening event candidate raw =>
    refine ⟨event, rfl, ?_⟩
    by_cases ready : state.config.cut.Ready event
    · by_cases timely : state.WithinDeadline runtime event
      · cases node : nodeView graph event with
        | sample payload law outputEq codeEq =>
          simp [handle, packet, ready, timely, node] at accepted
        | bind owner payload outputEq codeEq =>
          simp [handle, packet, ready, timely, node] at accepted
        | resolve owner payload binding checks outputEq codeEq =>
          have sender : message.sender = owner := by
            by_contra different
            simp [handle, packet, ready, timely, node, different] at accepted
          rw [sender]
          change (graph.nodes event).actor = some owner
          rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
          rfl
      · simp [handle, packet, ready, timely] at accepted
    · simp [handle, packet, ready] at accepted

end Vegas.EventGraphRuntime
