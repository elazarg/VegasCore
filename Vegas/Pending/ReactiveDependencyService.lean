/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveUniformResponse
import Vegas.Pending.ReactiveAuthorizationProgress

/-! # Dependency authorization enforced by public service history

Both the monitor and the uniform calendar use the original public submission
observation reconstructed by Interaction. No private recall is a service input.
These are ideal public-history services; a concrete ledger must supply comparable
authenticated evidence. The uniform calendar guarantees authorization and
at-most-once inclusion, with local response regularity. Completion and SPE
require further properties of the calendar and the compiled continuation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def dependencyCondition (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  view.DependenciesCompleted message.payload.call

def dependencyMonitor (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).Scheduler :=
  (runtime.reactiveApplication leaks).authorizedScheduler dependencyCondition scheduler

theorem dependencyMonitor_authorized (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    runtime.DependencyAuthorized leaks initial horizon
      (runtime.dependencyMonitor leaks scheduler) :=
  (runtime.reactiveApplication leaks).authorizedScheduler_requiresAuthorization
    ReactivePlayerView.publicView (fun _ _ => rfl) dependencyCondition initial horizon scheduler

/-- This predicate ignores hidden candidate values and raw opening contents. -/
def eventProposal (event : graph.EventId) (owner : Player)
    (message : Message Player (WitnessedPacket graph)) : Bool :=
  decide (message.sender = owner ∧ message.payload.call.event? graph = some event)

def dependencyUniformScheduler (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (calendar : Nat → (runtime.reactiveApplication leaks).UniformInstruction) :
    (runtime.reactiveApplication leaks).Scheduler :=
  (runtime.reactiveApplication leaks).uniformScheduler dependencyCondition calendar

theorem dependencyUniformScheduler_authorized (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (calendar : Nat → (runtime.reactiveApplication leaks).UniformInstruction) :
    runtime.DependencyAuthorized leaks initial horizon
      (runtime.dependencyUniformScheduler leaks calendar) :=
  (runtime.reactiveApplication leaks).uniformScheduler_requiresAuthorization
    ReactivePlayerView.publicView (fun _ _ => rfl) dependencyCondition initial horizon calendar

theorem dependencyUniformScheduler_atMostOnce (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (calendar : Nat → (runtime.reactiveApplication leaks).UniformInstruction) :
    (runtime.reactiveApplication leaks).AtMostOnce
      (runtime.dependencyUniformScheduler leaks calendar) :=
  (runtime.reactiveApplication leaks).uniformScheduler_atMostOnce dependencyCondition calendar

/-- The public verifier admits exactly the semantic dependency condition for
every actual pending envelope, at arbitrary initialized legal prefixes. -/
theorem dependencyPermission_iff (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (message : Message Player (WitnessedPacket graph))
    (pending : message ∈ control.execution.network.pending) :
    (runtime.reactiveApplication leaks).SubmissionPermitted dependencyCondition
        control.execution.environmentRecall message ↔
      control.execution.AuthorizedAtSubmission (runtime.reactiveApplication leaks)
        (runtime.submissionDependencyCondition leaks) message :=
  (runtime.reactiveApplication leaks).submissionPermitted_iff_authorized
    ReactivePlayerView.publicView dependencyCondition control.execution message
    (((runtime.reactiveApplication leaks).submissionAudit_history ReactivePlayerView.publicView
      (fun _ _ => rfl) initial horizon scheduler trace).1.pending message pending)

end Vegas.EventGraphRuntime
