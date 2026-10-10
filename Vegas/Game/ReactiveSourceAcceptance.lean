/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactivePacketEvidence

/-! # Acceptance of recorded compiled calls during their live event window -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An acceptable call actually retained from its author's response remains
acceptable at a later initialized trace while its event is unfinished and
timely. Independent private bindings may complete in the intervening time;
the conclusion does not assume the public store or accepted table unchanged. -/
theorem recordedSourceCall_accepted
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (runtime : EventGraphRuntime (toEventGraph program))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph program)))
    (inputs : PMF (toEventGraph program).Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (who : Player) (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (message : Message Player (WitnessedPacket (toEventGraph program)))
    (emitted : entry.emitted = some message)
    (conforming : runtime.freshServiceAcceptable entry.beforeView.application.publicView message)
    (event : (toEventGraph program).EventId)
    (named : message.payload.call.event? (toEventGraph program) = some event)
    (ready : entry.beforeView.application.publicView.EventReady event)
    (unfinished : event ∉ control.execution.application.config.cut.completed)
    (timely : control.execution.application.WithinDeadline runtime event) :
    ∃ next, (runtime.reactiveApplication leaks).handle control.execution.application message =
      some next := by
  have eventStable : EntryEventStable runtime leaks control.execution :=
    entryEventStable_history runtime leaks (inputs.map State.initial) horizon scheduler trace
  have storeStable : EntryStoreStable runtime leaks control.execution :=
    entryStoreStable_history runtime leaks (inputs.map State.initial) horizon scheduler trace
  have valid : control.execution.application.BindingInvariant :=
    runtime.reactiveBindingInvariant_history leaks inputs horizon scheduler trace
  have evidence : (runtime.packetEvidence leaks).Sound control.execution :=
    (runtime.packetEvidence leaks).history_sound (inputs.map State.initial) horizon scheduler trace
  obtain ⟨extra, order, together, _, acceptedChanged⟩ :=
    eventStable who entry retained event ready unfinished
  have output : message ∈ (runtime.reactiveApplication leaks).outputs
      (control.execution.recall who) := List.mem_filterMap.mpr ⟨entry, retained, emitted⟩
  have recall : control.execution.InputRecall (runtime.reactiveApplication leaks) :=
    (runtime.reactiveApplication leaks).history_inputRecall (inputs.map State.initial) horizon
      scheduler trace
  rw [← recall who] at output
  have certified : ∀ fact ∈ message.payload.evidence.toList,
      fact.Holds control.execution.application :=
    evidence.inputs message (List.mem_filter.mp output).1
  obtain ⟨next, accepted⟩ := runtime.freshServiceAcceptable_accepted_of_extends
    (toEventGraph_barrierOrdered program).revealRelaxedOrdered
    control.execution.application entry.beforeView.application.publicView message conforming
    event named order together acceptedChanged (storeStable who entry retained).2
    unfinished timely certified valid
  exact ⟨next, (runtime.reactiveApplication_handle_of_tokenValid leaks
    control.execution.application message conforming.tokenValid).trans accepted⟩

end Vegas
