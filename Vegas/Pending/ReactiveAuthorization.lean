/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAuthorization
import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventPublicState

/-! # Event dependencies at authenticated submission

The required certificate concerns completed predecessor instances in the
original submission view. Readiness at inclusion does not supply this fact.
This module defines the semantic service obligation and proves permanent
exclusion of premature envelopes under it. It does not construct a ledger
certificate or assume that the existing reserved service satisfies the contract.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Malformed unaddressed traffic has no dependency obligation; it cannot
complete an event. Addressed packets require all predecessors already completed. -/
def PublicView.DependenciesCompleted (view : PublicView graph) (packet : Payload graph) : Prop :=
  ∀ event, packet.event? graph = some event →
    ∀ predecessor ∈ graph.order.predecessors event,
      predecessor ∈ view.observation.completionOrder

def submissionDependencyCondition (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (message : Message Player (Payload graph)) : Prop :=
  view.application.publicView.DependenciesCompleted message.payload

/-- Dependency authorization uses the public completion identities and event
address only. It does not inspect a hidden value, opening, or private memory. -/
theorem submissionDependencyCondition_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (first second : (runtime.reactiveApplication leaks).PlayerView)
    (same : first.application.publicView.observation.completionOrder =
      second.application.publicView.observation.completionOrder)
    (left right : Message Player (Payload graph))
    (address : left.payload.event? graph = right.payload.event? graph) :
    runtime.submissionDependencyCondition leaks first left ↔
      runtime.submissionDependencyCondition leaks second right := by
  simp only [submissionDependencyCondition, PublicView.DependenciesCompleted, same, address]

def DependencyAuthorized (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) : Prop :=
  (runtime.reactiveApplication leaks).RequiresSubmissionAuthorization
    (runtime.submissionDependencyCondition leaks) initial horizon scheduler

theorem premature_not_authorized (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (message : Message Player (Payload graph))
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (found : execution.submissionOrigin? (runtime.reactiveApplication leaks)
      message.id = some entry)
    (event predecessor : graph.EventId) (address : message.payload.event? graph = some event)
    (dependency : predecessor ∈ graph.order.predecessors event)
    (missing : predecessor ∉ entry.beforeView.application.publicView.observation.completionOrder) :
    ¬ execution.AuthorizedAtSubmission (runtime.reactiveApplication leaks)
      (runtime.submissionDependencyCondition leaks) message := by
  rw [(runtime.reactiveApplication leaks).authorizedAtSubmission_iff _ _ message entry found]
  exact fun authorized => missing (authorized.2 event address predecessor dependency)

/-- Once an event is ready, a fresh submission has the required dependency
authorization. Inclusion and timely acceptance are separate service obligations. -/
theorem ready_submission_authorized (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (material : Submission graph) (event : graph.EventId)
    (address : material.packet.event? graph = some event)
    (ready : execution.application.publicView.EventReady event)
    (fresh : execution.submissionOrigin? (runtime.reactiveApplication leaks)
      (who, execution.network.nextSerial who) = none) :
    (execution.respond (runtime.reactiveApplication leaks) who
      ⟨some (.submit material)⟩).AuthorizedAtSubmission (runtime.reactiveApplication leaks)
        (runtime.submissionDependencyCondition leaks)
        ⟨(who, execution.network.nextSerial who), material.packet⟩ := by
  apply (runtime.reactiveApplication leaks).authorizedAtSubmission_submit
    _ _ who material fresh
  intro target same predecessor member
  have equal : event = target := Option.some.inj (address.symm.trans same)
  subst target
  exact ready.2 predecessor member

/-- Fresh authorization is available at every legal initialized prefix when
the event is ready, including after earlier deviations by arbitrary players. -/
theorem ready_submission_authorized_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (who : Player)
    (material : Submission graph) (event : graph.EventId)
    (address : material.packet.event? graph = some event)
    (ready : control.execution.application.publicView.EventReady event) :
    (control.execution.respond (runtime.reactiveApplication leaks) who
      ⟨some (.submit material)⟩).AuthorizedAtSubmission (runtime.reactiveApplication leaks)
        (runtime.submissionDependencyCondition leaks)
        ⟨(who, control.execution.network.nextSerial who), material.packet⟩ :=
  runtime.ready_submission_authorized leaks control.execution who material event address
    ready
    ((runtime.reactiveApplication leaks).submissionOrigin_next_none_history
      initial horizon scheduler control trace who)

/-- No future legal suffix can make a premature envelope executable under the
contract. This covers replay and changes to the current completion cut. -/
theorem premature_not_accepted (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (contract : runtime.DependencyAuthorized leaks initial horizon scheduler)
    {first last : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).History}
    {fuel : Nat}
    (path : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (runtime.reactiveApplication leaks).Control)
    (firstEq : first.state = some before) (lastEq : last.state = some after)
    (inactive : after.actor = none) (message : Message Player (Payload graph))
    (running : 0 < after.remaining)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (found : before.execution.submissionOrigin? (runtime.reactiveApplication leaks)
      message.id = some entry)
    (event predecessor : graph.EventId) (address : message.payload.event? graph = some event)
    (dependency : predecessor ∈ graph.order.predecessors event)
    (missing : predecessor ∉ entry.beforeView.application.publicView.observation.completionOrder)
    (pending : after.execution.network.lookup message.id = some message)
    (selected : .include message.id ∈ (scheduler after.execution.environmentRecall
      (after.execution.observeEnvironment (runtime.reactiveApplication leaks))).support) :
    handle runtime after.execution.application message = none :=
  (runtime.reactiveApplication leaks).unauthorized_not_accepted _ initial horizon scheduler contract
    path before after firstEq lastEq inactive running message entry found
    (runtime.premature_not_authorized leaks before.execution message entry found event predecessor
      address dependency missing) pending selected

end Vegas.EventGraphRuntime

-- OPEN OBLIGATION: Complete the dependency-authorized continuation argument
-- ReactiveDependencyService enforces this contract using public history and
-- supplies authorized uniform selection. Prove suitable calendars' usable owner
-- responses, completion, and continuation incentives. A ledger certificate
-- implementation is separate. The reserved epoch service is not certified here.
