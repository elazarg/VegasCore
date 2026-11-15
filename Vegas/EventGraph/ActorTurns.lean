module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Information

@[expose] public section

/-! # Unambiguous ready turns for an actor

Service that activates an actor can address a ready event unambiguously when
the actor has no other ready event. This condition permits other actors to act
concurrently and imposes no ordering on public information.
-/

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Whenever this event is ready, no distinct ready event has the same owner. -/
def OwnerSolitary (graph : Vegas.EventGraph Player L) (event : graph.EventId) : Prop :=
  ∀ (cut : graph.order.Cut) {other : graph.EventId} {who : Player},
    cut.Ready event → cut.Ready other →
      graph.actor? event = some who → graph.actor? other = some who → other = event

/-- Each actor has at most one ready event at every cut. Other actors may act concurrently. -/
def ActorSerial (graph : Vegas.EventGraph Player L) : Prop :=
  ∀ event, graph.OwnerSolitary event

theorem OwnerSolitary.ready_actor_unique {event other : graph.EventId}
    (unique : graph.OwnerSolitary event) (cut : graph.order.Cut)
    (ready : cut.Ready event) (otherReady : cut.Ready other) {who : Player}
    (actor : graph.actor? event = some who) (otherActor : graph.actor? other = some who) :
    other = event :=
  unique cut ready otherReady actor otherActor

theorem ActorSerial.ready_actor_unique (serial : graph.ActorSerial)
    (cut : graph.order.Cut) {event other : graph.EventId}
    (ready : cut.Ready event) (otherReady : cut.Ready other) {who : Player}
    (actor : graph.actor? event = some who) (otherActor : graph.actor? other = some who) :
    other = event :=
  serial event cut ready otherReady actor otherActor

end Vegas.EventGraph
