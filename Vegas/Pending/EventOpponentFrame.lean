/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventInvariant
import Vegas.Pending.AcceptedEventOwnership

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
