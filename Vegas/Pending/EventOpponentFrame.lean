/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant

/-! # Native frames for opponent-owned events

Pointwise frame facts used when a focal player takes native private or
submission actions while another player's event remains under analysis.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Acceptance authenticates the packet sender as the actor of the uniquely
addressed event. Thus player-authored traffic can complete only that player's
events; chance events are completed only by environment commands. -/
theorem handle_event_actor
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    ∃ event, Payload.event? graph message.payload = some event ∧
      graph.actor? event = some message.sender := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | resolve | sample => simp [handle, ready, timely, view] at accepted
          | bind owner payload outputEq codeEq =>
              simp only [handle, dite_eq_left ready, dite_eq_left timely, view] at accepted
              split at accepted
              · rename_i sender
                have codeActor := congrArg EventCode.actor codeEq
                rw [EventCode.actor_cast outputEq (graph.nodes event)] at codeActor
                refine ⟨event, rfl, ?_⟩
                simpa only [EventGraph.actor?, EventCode.actor, Message.sender] using
                  codeActor.trans (congrArg some sender.symm)
              · simp_all
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | opening event candidate raw =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | bind | sample => simp [handle, ready, timely, view] at accepted
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [handle, dite_eq_left ready, dite_eq_left timely, view] at accepted
              split at accepted
              · rename_i sender
                have codeActor := congrArg EventCode.actor codeEq
                rw [EventCode.actor_cast outputEq (graph.nodes event)] at codeActor
                refine ⟨event, rfl, ?_⟩
                simpa only [EventGraph.actor?, EventCode.actor, Message.sender] using
                  codeActor.trans (congrArg some sender.symm)
              · simp_all
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted

/-- Applying an accepted focal-authored packet cannot consume an event owned
by another player.  This is the completion-set form used by boundary frames. -/
theorem handle_opponent_completed_iff
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph))
    (event : graph.EventId) (owner : Player)
    (actor : graph.actor? event = some owner) (different : owner ≠ message.sender)
    (accepted : handle runtime state message = some next) :
    event ∈ next.config.cut.completed ↔ event ∈ state.config.cut.completed := by
  obtain ⟨completed, addressed, completedActor⟩ :=
    handle_event_actor runtime state next message accepted
  obtain ⟨stepped, steppedAddress, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  have same : stepped = completed := Option.some.inj (steppedAddress.symm.trans addressed)
  subst stepped
  have other : event ≠ completed := by
    intro same
    subst event
    rw [completedActor] at actor
    exact different (Option.some.inj actor.symm)
  rw [EventGraph.Config.step_cut state.config _ ready action next.config member,
    EventOrder.Cut.mem_complete]
  simp [other]

end Vegas.EventGraphRuntime
