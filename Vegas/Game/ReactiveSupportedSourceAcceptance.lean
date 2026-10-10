/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReactiveSourceAcceptance
import Vegas.Pending.ReactiveSampledAcceptance
import Vegas.Pending.ReactivePosteriorAlignment

/-! # Actual sampled source calls remain accepted during their live window -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A transmitting supported prescribed response at an initialized author
trace is accepted at a later initialized trace retaining its actual emitted
record, while its original event remains unfinished and timely. Packet
conformance, original event identity and binding provenance are all derived. -/
theorem supportedSourceResponse_accepted
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (runtime : EventGraphRuntime (toEventGraph program))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph program)))
    (inputs : PMF (toEventGraph program).Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (before current : (runtime.reactiveApplication leaks).Control)
    (beforeTrace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some before))
    (currentTrace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some current))
    (who : Player) (policy : (toEventGraph program).BehavioralPolicy who)
    (intentions : List (Option (toEventGraph program).Completion))
    (physical : (runtime.reactiveApplication leaks).Action)
    (remembered : (toEventGraph program).Completion)
    (supported : (physical, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy (before.execution.recall who)
        intentions (before.execution.observe (runtime.reactiveApplication leaks) who)).support)
    (material : WitnessedSubmission (toEventGraph program))
    (transmitted : physical.transmission = some material)
    (authorTimely : before.execution.application.WithinDeadline runtime remembered.event)
    (unfinished : remembered.event ∉ current.execution.application.config.cut.completed)
    (timely : current.execution.application.WithinDeadline runtime remembered.event)
    (retained :
      (⟨before.execution.observe (runtime.reactiveApplication leaks) who, physical,
        some ⟨(who, before.execution.network.nextSerial who),
          material.emit ((runtime.reactiveApplication leaks).submit before.execution.application
            who material) who (before.execution.network.known who)⟩⟩ :
        (runtime.reactiveApplication leaks).PlayerEntry) ∈ current.execution.recall who) :
    let message : Message Player (WitnessedPacket (toEventGraph program)) :=
      ⟨(who, before.execution.network.nextSerial who),
        material.emit ((runtime.reactiveApplication leaks).submit before.execution.application
          who material) who (before.execution.network.known who)⟩
    ∃ next, (runtime.reactiveApplication leaks).handle current.execution.application message =
      some next := by
  intro message
  let entry : (runtime.reactiveApplication leaks).PlayerEntry :=
    ⟨before.execution.observe (runtime.reactiveApplication leaks) who, physical, some message⟩
  have valid : before.execution.application.BindingInvariant :=
    runtime.reactiveBindingInvariant_history leaks inputs horizon scheduler beforeTrace
  have acceptable := runtime.prescribedReactiveResponse_emitted_acceptable leaks before.execution
    valid who policy (before.execution.recall who) intentions physical remembered supported
    authorTimely material transmitted
  have fresh := runtime.prescribedReactiveResponse_some_fresh leaks who policy
    (before.execution.recall who) intentions
    (before.execution.observe (runtime.reactiveApplication leaks) who) physical remembered supported
  have named : message.payload.call.event? (toEventGraph program) = some remembered.event := by
    rcases runtime.reactiveDecision_transmission leaks who remembered.event remembered.action
      (before.execution.observe (runtime.reactiveApplication leaks) who).application with
      quiet | ⟨sent, issued, target⟩
    · rw [← fresh.2.2, transmitted] at quiet
      cases quiet
    · rw [← fresh.2.2, transmitted] at issued
      cases Option.some.inj issued
      exact target
  have ready : entry.beforeView.application.publicView.EventReady remembered.event := by
    change runtime.freshServiceAcceptable
      entry.beforeView.application.publicView message at acceptable
    cases packet : message.payload.call with
    | malformed raw => simp [freshServiceAcceptable, freshServiceEnvelope, packet] at acceptable
    | commitment event candidate =>
        have same : event = remembered.event := by
          apply Option.some.inj
          simpa only [packet, Payload.event?] using named
        subst event
        simp only [freshServiceAcceptable, packet] at acceptable
        exact acceptable.1.1
    | opening event candidate raw =>
        have same : event = remembered.event := by
          apply Option.some.inj
          simpa only [packet, Payload.event?] using named
        subst event
        simp only [freshServiceAcceptable, freshServiceEnvelope, packet] at acceptable
        exact acceptable.1
  exact recordedSourceCall_accepted program runtime leaks inputs horizon scheduler current
    currentTrace who entry retained message rfl acceptable remembered.event named ready
    unfinished timely

end Vegas
