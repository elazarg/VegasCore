/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveIntentionRecall
import Vegas.Pending.EventInvariant
import Interaction.ReactiveTrafficIdentity

/-! # Original recall stability under actual message inclusion -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A new receipt cannot alter an original completion if every recorded
message addressed to that completed event receives only a rejecting receipt. -/
theorem reactiveOriginal_append_rejecting_event_receipt (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (receipts : List (MessageId Player × Bool)) (id : MessageId Player) (accepted : Bool)
    (completion : graph.Completion)
    (rejecting : ∀ entry ∈ history, ∀ message, entry.emitted = some message →
      message.payload.call.event? graph = some completion.event → message.id = id →
      accepted = false) :
    runtime.reactiveOriginal leaks who history intentions (receipts ++ [(id, accepted)])
      completion = runtime.reactiveOriginal leaks who history intentions receipts completion := by
  classical
  cases node : nodeView graph completion.event with
  | sample => simp only [reactiveOriginal, node]
  | bind => simp only [reactiveOriginal, node]
  | resolve =>
      simp only [reactiveOriginal, node]
      apply congrArg (fun entries : List graph.Completion => entries.head?.getD completion)
      apply List.filterMap_congr
      rintro ⟨entry, saved⟩ member
      cases saved with
      | none => rfl
      | some remembered =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          split
          · rfl
          · cases emitted : entry.emitted with
            | none => simp only [Option.bind_none]
            | some message =>
                simp only [Option.bind_some]
                by_cases named : message.payload.call.event? graph = some completion.event
                · have old : ((message.id, true) ∈ receipts ++ [(id, accepted)]) ↔
                      (message.id, true) ∈ receipts := by
                    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
                    constructor
                    · rintro (prior | ⟨same, positive⟩)
                      · exact prior
                      · have refused := rejecting entry (List.of_mem_zip member).1
                          message emitted named same
                        rw [refused] at positive
                        cases positive
                    · exact Or.inl
                  simp only [old]
                · simp only [named, false_and, and_false, ↓reduceIte]

/-- Including an actual network envelope preserves original recall at every
already completed event. Unique actual envelope identities force any new
receipt for that event to be rejecting. -/
theorem reactiveOriginal_include_completed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (unique : execution.network.UniqueIds)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (intentions : List (Option graph.Completion)) (id : MessageId Player)
    (completion : graph.Completion)
    (completed : completion.event ∈ execution.application.config.cut.completed) :
    let next := execution.includePending (runtime.reactiveApplication leaks) id
    runtime.reactiveOriginal leaks who (next.recall who) intentions next.receipts completion =
      runtime.reactiveOriginal leaks who (execution.recall who) intentions execution.receipts
        completion := by
  intro next
  cases found : execution.network.lookup id with
  | none =>
      simp only [next, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, found]
  | some envelope =>
      have envelopeId : envelope.id = id := by
        simpa using
          (List.find?_eq_some_iff_append.mp found).1
      have rejecting : ∀ entry ∈ execution.recall who, ∀ message,
          entry.emitted = some message →
          message.payload.call.event? graph = some completion.event → message.id = id →
          ((runtime.reactiveApplication leaks).handle execution.application envelope).isSome =
            false := by
        intro entry member message emitted named sameId
        have output : message ∈ (runtime.reactiveApplication leaks).outputs
            (execution.recall who) := List.mem_filterMap.mpr ⟨entry, member, emitted⟩
        rw [← recalled who] at output
        have input : message ∈ execution.network.inputs := (List.mem_filter.mp output).1
        have actual : envelope = message :=
          (unique.inputs message input).lookup id envelope found
            (envelopeId.trans sameId.symm)
        subst envelope
        have refused := handle_eq_none_of_completed runtime execution.application
          ⟨message.id, message.payload.call⟩ completion.event named completed
        simp only [reactiveApplication_handle, refused, ite_self, Option.isSome_none]
      simp only [next, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, found]
      exact runtime.reactiveOriginal_append_rejecting_event_receipt leaks who
        (execution.recall who) intentions execution.receipts id
        ((runtime.reactiveApplication leaks).handle execution.application envelope).isSome
        completion rejecting

/-- Inclusion stability with all network and recall invariants derived from
an actual initialized protocol trace. It holds for arbitrary supported private
memory, opposing clients and scheduler. -/
theorem reactiveOriginal_include_completed_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (who : Player) (intentions : List (Option graph.Completion)) (id : MessageId Player)
    (completion : graph.Completion)
    (completed : completion.event ∈ control.execution.application.config.cut.completed) :
    let next := control.execution.includePending (runtime.reactiveApplication leaks) id
    runtime.reactiveOriginal leaks who (next.recall who) intentions next.receipts completion =
      runtime.reactiveOriginal leaks who (control.execution.recall who) intentions
        control.execution.receipts completion := by
  exact runtime.reactiveOriginal_include_completed leaks who control.execution
    ((runtime.reactiveApplication leaks).uniqueIds_history scheduler
      (inputs.map State.initial) horizon control trace)
    ((runtime.reactiveApplication leaks).history_inputRecall (inputs.map State.initial)
      horizon scheduler trace) intentions id completion completed

end Vegas.EventGraphRuntime
