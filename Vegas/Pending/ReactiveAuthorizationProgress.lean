/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecallInvariant
import Vegas.Pending.ReactiveAuthorization
import Vegas.Pending.EventInvariant
import Vegas.EventGraph.CommutationRecall
import Vegas.EventGraph.BarrierInformation

/-! # Authorized packets belong to ready events

Completion identities in every remembered submission view are included in the
current completion cut. Consequently an authorized packet for an unfinished
event addresses a currently ready event. Under the source information discipline,
each player's authorized unfinished packets belong to its one ready owned event;
foreign hidden commitments can remain concurrent. This holds after arbitrary
deviations. It is not a continuation incentive theorem.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveCompletedInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (completed : Finset graph.EventId) :
    (runtime.reactiveApplication leaks).Invariant
      (fun state => completed ⊆ state.config.cut.completed) where
  submit state who material retained := by
    change completed ⊆
      (submitStep (material.register state who) who material.packet).config.cut.completed
    rw [submitStep_config, (material.register_facts who state).1]
    exact retained
  handle state message next retained accepted :=
    retained.trans (handle_completed_subset runtime state next message accepted)
  environment state command next retained supported :=
    retained.trans (environmentStep_completed_subset runtime state next command supported)

theorem submissionView_completed_subset (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (who : Player) (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (member : entry ∈ control.execution.recall who) :
    entry.beforeView.application.publicView.observation.completionOrder.toFinset ⊆
      control.execution.application.config.cut.completed := by
  apply (runtime.reactiveApplication leaks).recallBound_history
    (fun view => view.publicView.observation.completionOrder.toFinset)
    (fun state => state.config.cut.completed) _
    (runtime.reactiveCompletedInvariant leaks) initial horizon scheduler control trace
    who entry member
  intro state observer
  apply Finset.ext
  intro event
  exact List.mem_toFinset.trans (state.config.history_exact event)

theorem authorized_predecessor_completed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (message : Message Player (Payload graph))
    (authorized : control.execution.AuthorizedAtSubmission (runtime.reactiveApplication leaks)
      (runtime.submissionDependencyCondition leaks) message)
    (event predecessor : graph.EventId) (address : message.payload.event? graph = some event)
    (dependency : predecessor ∈ graph.order.predecessors event) :
    predecessor ∈ control.execution.application.config.cut.completed := by
  obtain ⟨entry, found, _, allowed⟩ := authorized
  exact runtime.submissionView_completed_subset leaks initial horizon scheduler control trace
    message.sender entry (List.mem_of_find?_eq_some found)
      (List.mem_toFinset.mpr (allowed event address predecessor dependency))

/-- An authorization created while an event was blocked cannot appear later
in the same envelope; before readiness there are no authorized packets for it. -/
theorem authorized_event_ready (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (message : Message Player (Payload graph))
    (authorized : control.execution.AuthorizedAtSubmission (runtime.reactiveApplication leaks)
      (runtime.submissionDependencyCondition leaks) message)
    (event : graph.EventId) (address : message.payload.event? graph = some event)
    (unfinished : event ∉ control.execution.application.config.cut.completed) :
    control.execution.application.config.cut.Ready event :=
  ⟨unfinished, fun predecessor member => runtime.authorized_predecessor_completed leaks
    initial horizon scheduler control trace message authorized event predecessor address member⟩

/-- Under sequential readiness, every authorized unfinished event packet
belongs to the current event. Raw future packets can still be pending/leaked. -/
theorem authorized_event_eq_current (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (current : graph.EventId)
    (unique : ∀ event, control.execution.application.config.cut.Ready event → event = current)
    (message : Message Player (Payload graph))
    (authorized : control.execution.AuthorizedAtSubmission (runtime.reactiveApplication leaks)
      (runtime.submissionDependencyCondition leaks) message)
    (event : graph.EventId) (address : message.payload.event? graph = some event)
    (unfinished : event ∉ control.execution.application.config.cut.completed) :
    event = current :=
  unique event (runtime.authorized_event_ready leaks initial horizon scheduler control trace
    message authorized event address unfinished)

/-- Global serialization is unnecessary for this exclusion. The graph's
information discipline already orders each player's own strategic events. -/
theorem authorized_owned_event_eq_current (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    {schema : graph.LogicalSchema} (discipline : graph.InformationDiscipline schema)
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (current : graph.EventId)
    (ready : control.execution.application.config.cut.Ready current)
    (message : Message Player (Payload graph))
    (currentActor : graph.actor? current = some message.sender)
    (authorized : control.execution.AuthorizedAtSubmission (runtime.reactiveApplication leaks)
      (runtime.submissionDependencyCondition leaks) message)
    (event : graph.EventId) (address : message.payload.event? graph = some event)
    (actor : graph.actor? event = some message.sender)
    (unfinished : event ∉ control.execution.application.config.cut.completed) :
    event = current := by
  by_contra different
  have eventReady := runtime.authorized_event_ready leaks initial horizon scheduler control trace
    message authorized event address unfinished
  exact discipline.ready_actor_ne eventReady ready different actor currentActor rfl

/-- Public-barrier source lowering supplies the required information discipline.
Foreign ready commitments remain concurrent and available to passive observation. -/
theorem barrier_authorized_owned_event_eq_current (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (ordered : graph.BarrierOrdered)
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (current : graph.EventId)
    (ready : control.execution.application.config.cut.Ready current)
    (message : Message Player (Payload graph))
    (currentActor : graph.actor? current = some message.sender)
    (authorized : control.execution.AuthorizedAtSubmission (runtime.reactiveApplication leaks)
      (runtime.submissionDependencyCondition leaks) message)
    (event : graph.EventId) (address : message.payload.event? graph = some event)
    (actor : graph.actor? event = some message.sender)
    (unfinished : event ∉ control.execution.application.config.cut.completed) :
    event = current :=
  runtime.authorized_owned_event_eq_current leaks ordered.informationDiscipline initial horizon
    scheduler control trace current ready message currentActor authorized event address actor
    unfinished

end Vegas.EventGraphRuntime
