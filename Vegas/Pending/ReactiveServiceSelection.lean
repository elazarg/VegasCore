/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePacketIntegrity
import Vegas.Pending.ReactiveServiceProgress
import Interaction.ReactiveSubmissionAudit

/-! # Actual reserved selection and timing during reactive service

The selector uses authenticated authors, event addresses, and spent identifiers.
Packet integrity makes its choice independent of competing traffic and replay
when the prescribed event envelope is still pending and unpublished. Zero-tick
service prefixes retain the deadline of any event they have not completed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveLatest_last (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (prior : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph))
    (pending : view.network.pending = prior ++ [message])
    (authored : message.sender = who)
    (addressed : message.payload.call.event? graph = some event)
    (unpublished : view.Unpublished (runtime.reactiveApplication leaks) message.id) :
    runtime.reactiveLatest leaks event who view = .include message.id := by
  unfold reactiveLatest
  rw [pending]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.find?_cons, authored, addressed, unpublished, and_self, decide_true]

/-- An immediate reserved inclusion selects the fresh response, even after
arbitrary earlier competing packets from the same owner. -/
theorem reactiveLatest_after_submit (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (serials : execution.network.SerialsBeforeNext)
    (submission : WitnessedSubmission graph)
    (addressed : submission.call.packet.event? graph = some event) :
    runtime.reactiveLatest leaks event who
      ((execution.respond (runtime.reactiveApplication leaks) who
        ⟨some (.submit submission)⟩).observeEnvironment (runtime.reactiveApplication leaks)) =
      .include (who, execution.network.nextSerial who) := by
  apply runtime.reactiveLatest_last leaks who event _ execution.network.pending
    ⟨(who, execution.network.nextSerial who), submission.emit
      (submitStep (submission.call.register execution.application who) who submission.call.packet)
        who (execution.network.known who)⟩ rfl rfl
  · exact addressed
  · exact serials.next_unpublished who

theorem reactiveLatest_prescribed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (integrity : runtime.ReactivePacketIntegrity leaks who execution)
    (message : Message Player (WitnessedPacket graph))
    (emitted : message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall who))
    (authored : message.sender = who)
    (addressed : message.payload.call.event? graph = some event)
    (pending : message ∈ execution.network.pending)
    (unpublished : (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
      (runtime.reactiveApplication leaks) message.id) :
    runtime.reactiveLatest leaks event who
      (execution.observeEnvironment (runtime.reactiveApplication leaks)) = .include message.id := by
  have unique := integrity.retained runtime leaks who execution message event emitted addressed
  unfold reactiveLatest
  split
  · rename_i absent
    have excluded := List.find?_eq_none.mp absent message (List.mem_reverse.mpr pending)
    simp only [authored, addressed, unpublished, and_self, decide_true] at excluded
    contradiction
  · rename_i selected found
    have selectedMem := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
    have selectedGood : selected.sender = who ∧
        selected.payload.call.event? graph = some event ∧
        (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
          (runtime.reactiveApplication leaks) selected.id := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    have same := unique.pending selected selectedMem selectedGood.1 selectedGood.2.1
    exact congrArg ReactiveApplication.Command.include (congrArg Message.id same)

theorem interaction_includeLatest_prescribed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (integrity : runtime.ReactivePacketIntegrity leaks who execution)
    (message : Message Player (WitnessedPacket graph))
    (emitted : message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall who))
    (authored : message.sender = who)
    (addressed : message.payload.call.event? graph = some event)
    (pending : message ∈ execution.network.pending)
    (unpublished : (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
      (runtime.reactiveApplication leaks) message.id) :
    (runtime.interactionStep leaks players network (.includeLatest event who) execution).map
        (fun next => next.application) =
      FinDist.pure
        (execution.includePending (runtime.reactiveApplication leaks) message.id).application := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind]
  rw [runtime.reactiveLatest_prescribed leaks who event execution integrity message emitted authored
    addressed pending unpublished]
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, FinDist.map_pure]

omit [DecidableEq Player] in
/-- A zero-tick segment cannot age an unfinished event out of its deadline. -/
theorem State.ServiceProgress.ready_timely_or_completed (runtime : EventGraphRuntime graph)
    {inputs : graph.Inputs} {before after : State graph}
    (progress : State.ServiceProgress inputs 0 before after)
    (event : graph.EventId) (ready : before.config.cut.Ready event)
    (timely : before.WithinDeadline runtime event) :
    event ∈ after.config.cut.completed ∨
      (after.config.cut.Ready event ∧ after.WithinDeadline runtime event) := by
  rcases progress.ready_or_completed event ready with done | stillReady
  · exact Or.inl done
  · refine Or.inr ⟨stillReady, ?_⟩
    cases activated : before.activatedAt event with
    | none => simp only [State.WithinDeadline, activated] at timely
    | some entered =>
        rw [State.WithinDeadline, progress.activated event entered activated stillReady.1,
          progress.clock, Nat.add_zero]
        simpa only [State.WithinDeadline, activated] using timely

/-- This applies in particular to every prefix of the actual wire block
between the reserved response and inclusion; opponent responses are arbitrary. -/
theorem runInteractionPlan_ready_timely (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.Invariant inputs) (zero : serviceTicks plan = 0)
    (event : graph.EventId) (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (reached : next ∈ (runtime.runInteractionPlan leaks players network plan execution).support) :
    event ∈ next.application.config.cut.completed ∨
      (next.application.config.cut.Ready event ∧
        next.application.WithinDeadline runtime event) := by
  have progress := runtime.runInteractionPlan_facts leaks inputs players network plan
    execution next valid reached
  rw [zero] at progress
  exact progress.ready_timely_or_completed runtime event ready timely

end Vegas.EventGraphRuntime
