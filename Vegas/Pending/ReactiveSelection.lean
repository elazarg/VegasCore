/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSelection
import Vegas.Pending.EventPublicState
import Vegas.Pending.ReactiveStateInvariant

/-! # Public commitment eligibility and regular native responses

Binding eligibility is the application's public acceptance test, scoped to one
event. Selection excludes spent envelope identifiers. All native response forms
satisfy regularity when the priority law is held fixed, including invalid and
unopenable commitments. The selector cannot inspect hidden commitment meanings.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
def bindingEligible (runtime : EventGraphRuntime graph) (view : PublicView graph)
    (event : graph.EventId) (packet : Message Player (Payload graph)) : Bool :=
  decide (packet.payload.event? graph = some event ∧ view.BindingIncludable runtime packet)

theorem bindingEligible_accepts (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (packet : Message Player (Payload graph))
    (eligible : runtime.bindingEligible state.publicView event packet = true) :
    (handle runtime state packet).isSome := by
  classical
  have valid := (of_decide_eq_true eligible).2
  rcases packet with ⟨id, payload⟩
  cases payload with
  | commitment addressed candidate =>
      exact (state.publicView_bindingIncludable runtime id addressed candidate).mp valid
  | opening addressed candidate raw | withhold addressed | malformed raw => cases valid

def bindingSelection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (priorities : FinDist (LinearOrder (MessageId Player))) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    FinDist (Option (MessageId Player)) :=
  (runtime.reactiveApplication leaks).prioritySelection priorities
    (fun message => runtime.bindingEligible execution.application.publicView event
      ⟨message.id, message.payload.call⟩) execution

/-- Player computation and optional transmission leave the public application
test unchanged; the comparison uses the actual state after the response. -/
theorem bindingSelection_response_regular (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (priorities : FinDist (LinearOrder (MessageId Player))) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (retained : execution.network.PendingOrPublished) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    (runtime.bindingSelection leaks priorities event execution).RegularAt
      (runtime.bindingSelection leaks priorities event
        (execution.respond (runtime.reactiveApplication leaks) who action))
      (some (who, execution.network.nextSerial who)) := by
  unfold bindingSelection
  rw [(runtime.reactive_respond_application leaks execution who action).2]
  exact (runtime.reactiveApplication leaks).prioritySelection_response_regular
    priorities _ execution retained who action

theorem bindingSelection_history_regular (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (initial : FinDist (State graph)) (horizon : Nat)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (priorities : FinDist (LinearOrder (MessageId Player))) (event : graph.EventId)
    (who : Player) (action : (runtime.reactiveApplication leaks).Action) :
    (runtime.bindingSelection leaks priorities event control.execution).RegularAt
      (runtime.bindingSelection leaks priorities event
        (control.execution.respond (runtime.reactiveApplication leaks) who action))
      (some (who, control.execution.network.nextSerial who)) :=
  runtime.bindingSelection_response_regular leaks priorities event control.execution
    ((runtime.reactiveApplication leaks).pendingOrPublished_history
      scheduler initial horizon trace) who action

/-- Selection is independent of the private binding value at a fixed handle
and fixed transport attributes, including when that binding is unopenable. -/
theorem bindingSelection_value_independent (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (priorities : FinDist (LinearOrder (MessageId Player)))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (event selectedEvent : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    runtime.bindingSelection leaks priorities selectedEvent
        (execution.respond (runtime.reactiveApplication leaks) who
          (runtime.reactiveBinding leaks who event payload first serial)) =
      runtime.bindingSelection leaks priorities selectedEvent
        (execution.respond (runtime.reactiveApplication leaks) who
          (runtime.reactiveBinding leaks who event payload second serial)) := by
  unfold bindingSelection
  rw [(runtime.reactive_respond_application leaks execution who
      (runtime.reactiveBinding leaks who event payload first serial)).2,
    (runtime.reactive_respond_application leaks execution who
      (runtime.reactiveBinding leaks who event payload second serial)).2]
  rfl

end Vegas.EventGraphRuntime
