/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveEmissionTokens
import Vegas.Pending.ReactiveEntryStability
import Vegas.Pending.ReactiveServiceProgress

/-! # Readiness and deadlines of authentic token-bearing packets -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Authentic readiness tokens certify physical readiness until the named event completes. -/
theorem ready_of_authentic_token (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (message : Message Player (WitnessedPacket graph))
    (authentic : message ∈ control.execution.network.inputs)
    (valid : message.payload.tokenValid = true) (event : graph.EventId)
    (named : message.payload.call.event? graph = some event)
    (unfinished : event ∉ control.execution.application.config.cut.completed) :
    control.execution.application.config.cut.Ready event := by
  obtain ⟨entry, member, emitted, _⟩ :=
    (runtime.history_network_tokens leaks initial horizon scheduler trace).inputs message authentic
  obtain ⟨issued, issuedCall, attached⟩ := (WitnessedPacket.tokenValid_iff _).mp valid
  have same : issued = event := Option.some.inj (issuedCall.symm.trans named)
  subst issued
  have prerequisites := (runtime.history_emission_token_issued leaks initial horizon scheduler
    trace message.sender entry member message emitted ⟨event⟩ attached).2
  have stable := runtime.entryStable_history leaks initial horizon scheduler trace
  refine ⟨unfinished, fun prior required => ?_⟩
  apply (control.execution.application.config.history_exact prior).mp
  exact (stable message.sender entry member).1.subset (prerequisites prior required)

omit [DecidableEq Player] in
/-- An unfinished ready owned event keeps its activation time, so a later timely
state certifies timeliness at the earlier service prefix. -/
theorem State.ServiceProgress.withinDeadline_before
    (runtime : EventGraphRuntime graph) {inputs : graph.Inputs} {ticks : Nat}
    {before after : State graph} (progress : State.ServiceProgress inputs ticks before after)
    (invariant : before.Invariant inputs) (event : graph.EventId)
    (ready : before.config.cut.Ready event) (owned : (graph.actor? event).isSome = true)
    (unfinished : event ∉ after.config.cut.completed)
    (timely : after.WithinDeadline runtime event) : before.WithinDeadline runtime event := by
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
    ((invariant.activated_iff event).mpr ⟨ready, owned⟩)
  have retained := progress.activated event entered activated unfinished
  simp only [State.WithinDeadline, activated] at ⊢
  simp only [State.WithinDeadline, retained] at timely
  have clock := progress.clock
  omega

end Vegas.EventGraphRuntime
