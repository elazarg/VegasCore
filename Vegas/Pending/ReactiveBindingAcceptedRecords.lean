/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSubmittedRecords
import Vegas.Pending.ReactiveAcceptedOutput

/-! # Successful accepted outputs from submitted binding records

Signed acceptance identifies an original submission. The submitted-binding
record fixes its repaired candidate to a typed success, and runtime association
provenance reads that value back from the accepted output.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- Every accepted own binding output is successful when the original signed
submissions are recorded by a repair with the same accepted handle table. -/
theorem RecordsSubmittedBindings.accepted_output_succeeded
    {memory : BindingMemory runtime leaks} {who : Player}
    {original repaired : (runtime.reactiveApplication leaks).Execution}
    (recorded : memory.RecordsSubmittedBindings runtime leaks who original repaired)
    (signed : SignedCommitments runtime leaks original)
    (count : runtime.CountRecall leaks original)
    (valid : repaired.application.BindingInvariant)
    (acceptedEq : repaired.application.accepted = original.application.accepted)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (accepted : repaired.application.accepted (.inr event) ≠ none) :
    OutputSucceeded repaired.application.config.store event := by
  obtain ⟨candidate, installedReverse⟩ := Option.ne_none_iff_exists.mp accepted
  have installed : repaired.application.accepted (.inr event) = some candidate :=
    installedReverse.symm
  have originalInstalled : original.application.accepted (.inr event) = some candidate := by
    rw [← acceptedEq]
    exact installed
  obtain ⟨otherPayload, candidateType⟩ := valid.accepted_typed _ candidate installed
  have types : EventField.binding candidate.1 otherPayload = .binding who payload :=
    candidateType.symm.trans outputEq
  have ownerEq : candidate.1 = who := (EventField.binding.inj types).1
  obtain ⟨message, emitted, call⟩ := signed.acceptedSigned event candidate originalInstalled
  rw [ownerEq, ← count.1 who] at emitted
  obtain ⟨input, sent⟩ := List.mem_filter.mp emitted
  have sender : message.sender = who := by simpa using sent
  have codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind who payload := by
    generalize cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) = code
    cases code
    rfl
  have node := nodeView_eq_bind outputEq codeEq
  obtain ⟨_, _, _, ⟨value, success⟩, _⟩ :=
    recorded message input sender event candidate call payload outputEq codeEq node
  have fixed := (State.bindingResult_eq_success_iff repaired.application candidate payload
    value).mp success
  let ref : FieldRef graph.layout (.binding who payload) := ⟨.inr event, outputEq⟩
  exact outputSucceeded_of_ref repaired.application.config.store event ref rfl
    (valid.opening_stored ref candidate value installed fixed) (fun failed => by cases failed)

end Vegas.EventGraphRuntime.BindingMemory
