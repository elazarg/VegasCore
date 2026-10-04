/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveService
import Vegas.Pending.EventPublicState

/-! # The asynchronous service contract

An environment scheduler of the reactive runtime already chooses every command
from the public environment history: whom to activate, which packet to
include, when to advance the clock, when to expire or sample. The asynchronous
chain model is therefore a contract on schedulers, not a new runtime. A *slot*
is the time between two clock advances, so the public clock counts slots.

The contract has per-event bounds. `delay event` bounds how many slots an
owned event may be ready before its owner is activated, and `bound event` how
many slots an owner's latest packet for a ready event may wait for inclusion.
Together they make a prescribed packet timely when
`delay event + bound event < runtime.deadline event`.

Every requirement quantifies over all legal histories of the raw protocol,
including those in which players deviate. The scheduler is exogenous: it is
fixed with the service and reads only the public environment view.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Some recorded activation of `owner` saw `event` ready, in the readiness
episode that started at clock `entered`. -/
def OwnerActivatedSince (history : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (event : graph.EventId) (owner : Player) (entered : Nat) : Prop :=
  ∃ entry ∈ history, entry.command = .activate owner ∧
    entry.beforeView.application.activatedAt event = some entered ∧
    entry.beforeView.application.EventReady event

/-- **Opportunity within `delay`.** Once an owned event has been ready for more
than `delay event` slots, its owner has been activated since it became ready.
Further activations of anyone are allowed. -/
def Opportunity (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay : graph.EventId → Nat) : Prop :=
  ∀ (control : (runtime.reactiveApplication leaks).Control),
    ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control) →
    ∀ event owner entered, graph.actor? event = some owner →
      control.execution.application.publicView.EventReady event →
      control.execution.application.activatedAt event = some entered →
      entered + delay event < control.execution.application.clock →
      OwnerActivatedSince runtime leaks control.execution.environmentRecall event owner entered

/-- `entry` emitted a packet authored by the author of `id`, addressed to
`event`, whose identifier is not `id`: another identifier of the same author
for the same event. Relayed packets of other authors do not count. -/
def EmitsOtherFor (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) (id : MessageId Player) : Prop :=
  ∃ message, entry.emitted = some message ∧ message.sender = id.1 ∧
    message.payload.call.event? graph = some event ∧ message.id ≠ id

/-- **Protected inclusion within `bound`.** When an owner has authored a
packet addressed to its event while the event was ready at clock `sent`, and
every packet of its own that the owner ever emits for that event carries the
same identifier,
that packet has a receipt once the clock passes `sent + bound event`, unless the
event has completed. Including any other packet, in any order, is allowed.

Only an owner's sole identifier is protected. Replays keep the original author
and identifier, so anyone, the owner included, can re-queue copies of an
owner's packet, and every copy carries its identifier. A prescribed owner
submits one packet of its own per event and may replay it. Relaying another
player's packet, even one addressed to the owner's event, does not void the
protection: the builder distinguishes authors by signature. An owner that
emits several identifiers of its own for one event deviates from every
prescribed client, and what the scheduler then includes is part of that
deviation's law, not a guarantee of the contract. -/
def ProtectedInclusion (initial : PMF (runtime.reactiveApplication leaks).State)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (bound : graph.EventId → Nat) : Prop :=
  ∀ (control : (runtime.reactiveApplication leaks).Control),
    ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control) →
    ∀ event owner, graph.actor? event = some owner →
    ∀ (earlier later : List (runtime.reactiveApplication leaks).PlayerEntry) entry message,
      control.execution.recall owner = earlier ++ entry :: later →
      entry.emitted = some message → message.sender = owner →
      message.payload.call.event? graph = some event →
      entry.beforeView.application.publicView.EventReady event →
      (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor runtime leaks other event message.id) →
      event ∉ control.execution.application.config.cut.completed →
      entry.beforeView.application.publicView.clock + bound event <
        control.execution.application.clock →
      ∃ accepted, (message.id, accepted) ∈ control.execution.receipts

/-- **Complete play.** Every legal terminal state has completed every event:
the scheduler eventually samples, includes or expires each one. -/
def CompletesPlay (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) : Prop :=
  ∀ (control : (runtime.reactiveApplication leaks).Control),
    ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control) →
    ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).terminal
      (some control) →
    control.execution.application.config.cut.Terminal

/-- The asynchronous service contract for a fixed horizon and scheduler, with
per-event reaction bounds `delay` and inclusion bounds `bound`. Finite
branching of the scheduler is a separate instance (`FiniteNature`). -/
structure AsyncContract (initial : PMF (runtime.reactiveApplication leaks).State)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay bound : graph.EventId → Nat) : Prop where
  opportunity : Opportunity runtime leaks initial horizon scheduler delay
  inclusion : ProtectedInclusion runtime leaks initial horizon scheduler bound
  completes : CompletesPlay runtime leaks initial horizon scheduler

/-- Every owned event leaves room for one reaction and one inclusion before its
deadline. -/
def AsyncTimely (delay bound : graph.EventId → Nat) : Prop :=
  ∀ event, (graph.actor? event).isSome → delay event + bound event < runtime.deadline event

end Vegas.EventGraphRuntime
