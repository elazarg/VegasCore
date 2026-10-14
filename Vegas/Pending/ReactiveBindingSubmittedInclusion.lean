/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSubmittedRecords
import Vegas.Pending.ReactiveSignedCommitments

/-! # Actual pending inclusion from recorded submission provenance -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {who : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- An actual retained envelope is one of the signed global inputs. This
uses author recall conservation and transmission provenance only. -/
theorem input_of_lookup (count : runtime.CountRecall leaks original)
    (provenance : original.Provenance (runtime.reactiveApplication leaks))
    (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : original.network.lookup id = some message) : message ∈ original.network.inputs := by
  obtain ⟨entry, member, material, _, emitted, _⟩ := provenance.lookup id message found
  have output : message ∈ (runtime.reactiveApplication leaks).outputs
      (original.recall message.sender) := List.mem_filterMap.mpr ⟨entry, member, emitted⟩
  rw [← count.1 message.sender] at output
  exact (List.mem_filter.mp output).1

/-- The pending binding's remembered action, remembered value and fixed
candidate facts follow from its actual signed submission. -/
theorem RecordsSubmittedBindings.pending_binding
    (recorded : memory.RecordsSubmittedBindings runtime leaks who original repaired)
    (count : runtime.CountRecall leaks original)
    (provenance : original.Provenance (runtime.reactiveApplication leaks))
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph)
    (sender : id.1 = who)
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩) :
    memory.shadow.RecordsBinding event outputEq
        (original.application.bindingResult candidate payload) ∧
      original.application.candidates.lookup candidate ≠ .fresh ∧
      repaired.application.candidates.lookup candidate ≠ .fresh ∧
      (∃ value, repaired.application.bindingResult candidate payload = .success value) ∧
      ∀ value, original.application.bindingResult candidate payload = .success value →
        repaired.application.bindingResult candidate payload = .success value := by
  exact recorded _ (input_of_lookup count provenance id _ found) sender
    event candidate rfl payload outputEq codeEq node

/-- Real delayed inclusion preserves the frame using submission facts carried
by the invariant; no separate remembered-result premise is required. -/
theorem Frame.recorded_binding_inclusion
    (frame : Frame runtime leaks memory who original repaired)
    (recorded : memory.RecordsSubmittedBindings runtime leaks who original repaired)
    (count : runtime.CountRecall leaks original)
    (provenance : original.Provenance (runtime.reactiveApplication leaks))
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph)
    (sender : id.1 = who) (owned : candidate.1 = who)
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (vacant : original.application.accepted (.inr event) = none)
    (unused : original.application.HandleUnused candidate) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory who
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  obtain ⟨remembered, firstFixed, secondFixed, _, successes⟩ :=
    recorded.pending_binding count provenance event payload outputEq codeEq node id candidate
      sender found
  exact frame.pending_binding_inclusion event payload outputEq codeEq node id candidate sender
    owned found ready timely vacant unused firstFixed secondFixed remembered.1 remembered.2
    successes

end Vegas.EventGraphRuntime.BindingMemory
