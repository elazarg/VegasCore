/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFiniteResponses

/-! # Late sends that fail with a known probability

A builder satisfying the asynchronous contract protects an owner's first
packet for a ready event. A packet the owner sends later, after an earlier
activation at which the event was already ready, has no such protection; a
builder-first deposit can be sized against it only when its inclusion is known
not to be sure. `Vegas.EventGraphRuntime.LateSendsFailAtLeast` states that
floor: at every reachable history of the bounded raw runtime, every late
packet ends without an accepting receipt with conditional probability at least
the floor, under every behavioral continuation of all players. The floor is a
hypothesis on the builder, never derived from the contract; a builder whose
late inclusions are sure has floor zero.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Protocol Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- `entry` emits `message` for `event` after an earlier activation of the same
player at which the event was already ready: a late send. -/
def LateSend (event : graph.EventId)
    (earlier : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  entry.emitted = some message ∧ message.payload.call.event? graph = some event ∧
    ∃ previous ∈ earlier, previous.beforeView.application.publicView.EventReady event

/-- **Late sends fail with probability at least `floor`.** At every reachable
history of the bounded raw runtime in which an owner has sent a late packet
for one of its events, under every behavioral continuation of all players,
terminal play gives that packet no accepting receipt with probability at
least `floor`. -/
def LateSendsFailAtLeast (bounds : MessageBounds graph)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (floor : ℝ) : Prop :=
  let menu := bounds.rawMenu runtime leaks
  let model := menu.information initial horizon scheduler
  let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
  ∀ (profile : ∀ who, model.BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (control : (runtime.reactiveApplication leaks).Control), history.state = some control →
    ∀ (event : graph.EventId) (owner : Player), graph.actor? event = some owner →
    ∀ (earlier later : List (runtime.reactiveApplication leaks).PlayerEntry)
      (entry : (runtime.reactiveApplication leaks).PlayerEntry)
      (message : Message Player (WitnessedPacket graph)),
      control.execution.recall owner = earlier ++ entry :: later →
      message.sender = owner → runtime.LateSend leaks event earlier entry message →
      floor ≤ ((model.runBehavioralTerminalFrom certificate profile history).toOuterMeasure
        {final | ∀ control', final.state = some control' →
          (message.id, true) ∉ control'.execution.receipts}).toReal

end Vegas.EventGraphRuntime
