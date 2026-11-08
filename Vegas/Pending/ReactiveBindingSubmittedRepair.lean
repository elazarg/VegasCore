/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingSubmittedRecords
import Vegas.Pending.ReactiveBindingWindowLaw

/-! # Submission provenance under actual binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory timeouts leaks} {who : Player}
  {original repaired : ((reactiveApplication timeouts) leaks).Execution}

/-- Every repaired fresh owned binding prepares an opening of the event's
actual payload type, including absent and wrongly typed original material. -/
theorem Frame.binding_submission_succeeds
    (frame : Frame timeouts leaks memory who original repaired)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let app := (reactiveApplication timeouts) leaks
    let changed := memory.repairResponse timeouts leaks who (repaired.observe app who)
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
    ∃ value, (repaired.respond app who changed.1).application.bindingResult
      (who, .prepared serial) payload = .success value := by
  let app := (reactiveApplication timeouts) leaks
  let view := repaired.observe app who
  have actualFresh := (frame.slots (.prepared serial)).mp fresh
  have ownFresh : (memory.shadow.inputView timeouts leaks view).application.candidates
      (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  let response : app.Action :=
    ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
  change ∃ value, (repaired.respond app who
    (memory.repairResponse timeouts leaks who view response).1).application.bindingResult
      (who, .prepared serial) payload = .success value
  dsimp only [response]
  cases decoded : opening.bind (fun raw => raw.as? payload) with
  | none =>
      rw [memory.repairResponse_unusable timeouts leaks who view event payload outputEq codeEq
        node serial opening ownFresh actualFresh decoded]
      exact ⟨L.someValue payload, (reactiveBinding_result timeouts) leaks who event payload
        (.success (L.someValue payload)) serial repaired actualFresh⟩
  | some value =>
      rw [memory.repairResponse_usable timeouts leaks who view event payload outputEq codeEq
        node serial opening ownFresh actualFresh value decoded]
      exact ⟨value, ((submitted_bindingResult timeouts) leaks repaired who event payload serial
        opening actualFresh).trans (by simp only [decoded, Option.elim_some])⟩

/-- Count-admitted fresh binding repair extends the concrete submission
provenance invariant. First-for-event prevents overwriting any earlier record;
fixed candidates preserve every earlier prepared meaning on both sides. -/
theorem RecordsSubmittedBindings.binding_submission
    (recorded : memory.RecordsSubmittedBindings timeouts leaks who original repaired)
    (frame : Frame timeouts leaks memory who original repaired)
    (count : (CountRecall timeouts) leaks original)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (who, .prepared serial) = .fresh)
    (permitted : countPermits
      (((reactiveApplication timeouts) leaks).outputs (original.logs who))
      ((localEnvelope timeouts) leaks who (original.logs who)
        (original.observe ((reactiveApplication timeouts) leaks) who)
        ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩) = true) :
    let app := (reactiveApplication timeouts) leaks
    let view := repaired.observe app who
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
    let changed := memory.repairResponse timeouts leaks who view response
    let nextMemory : BindingMemory timeouts leaks :=
      ⟨changed.2, memory.responses ++ [(memory.shadow.inputView timeouts leaks view, response)]⟩
    nextMemory.RecordsSubmittedBindings timeouts leaks who
      (original.respond app who response) (repaired.respond app who changed.1) := by
  let app := (reactiveApplication timeouts) leaks
  let view := repaired.observe app who
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩
  let response : app.Action := ⟨some material⟩
  let changed := memory.repairResponse timeouts leaks who view response
  let nextMemory : BindingMemory timeouts leaks :=
    ⟨changed.2, memory.responses ++ [(memory.shadow.inputView timeouts leaks view, response)]⟩
  let left := original.respond app who response
  let right := repaired.respond app who changed.1
  have ownFresh : (memory.shadow.inputView timeouts leaks view).application.candidates
      (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  have actualFresh := (frame.slots (.prepared serial)).mp fresh
  have localFresh : view.application.candidates (.prepared serial) = .fresh := actualFresh
  have pending := frame.binding_submission_pending event payload outputEq codeEq node
    serial opening fresh
  have succeeds := frame.binding_submission_succeeds event payload outputEq codeEq node
    serial opening fresh
  change nextMemory.RecordsSubmittedBindings timeouts leaks who left right
  intro message member sender other candidate call domain otherOutput otherCode otherNode
  have inputs := ((countPermits_respond timeouts) leaks original count who material).1
  change message ∈ left.network.inputs at member
  rw [inputs, List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · obtain ⟨remembered, firstFixed, secondFixed, oldSucceeds, successes⟩ :=
      recorded message prior sender other candidate call domain otherOutput otherCode otherNode
    have different := priorBinding_ne_of_permitted timeouts leaks original count who event serial
      opening permitted message prior sender other candidate call
    have firstStable : left.application.candidates.lookup candidate =
        original.application.candidates.lookup candidate :=
      (reactive_respond_candidate_fixed timeouts) leaks original who response candidate firstFixed
    have secondStable : right.application.candidates.lookup candidate =
        repaired.application.candidates.lookup candidate :=
      (reactive_respond_candidate_fixed timeouts) leaks repaired who changed.1 candidate secondFixed
    have firstResult : left.application.bindingResult candidate domain =
        original.application.bindingResult candidate domain := by
      unfold State.bindingResult
      rw [firstStable]
    have secondResult : right.application.bindingResult candidate domain =
        repaired.application.bindingResult candidate domain := by
      unfold State.bindingResult
      rw [secondStable]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have retained := (remembered.rememberCandidate (.prepared serial)
          (material.call.candidateAfter who
            (memory.shadow.inputView timeouts leaks view).application.candidates
              (.prepared serial))).rememberCompletion_of_ne event different
          (cast (congrArg EventField.Action outputEq.symm)
            (some ((opening.bind fun raw => raw.as? payload).elim .failure
              PublicationResult.success)))
          (cast (congrArg EventField.Value outputEq.symm)
            ((opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success))
      change changed.2.RecordsBinding other otherOutput _
      simp only [changed, repairResponse, response, material, node, ownFresh, localFresh,
        and_self, ↓reduceIte]
      rw [firstResult]
      exact retained
    · change left.application.candidates.lookup candidate ≠ .fresh
      rwa [firstStable]
    · change right.application.candidates.lookup candidate ≠ .fresh
      rwa [secondStable]
    · rw [secondResult]
      exact oldSucceeds
    · rw [firstResult, secondResult]
      exact successes
  · change Payload.commitment event (who, .prepared serial) = .commitment other candidate at call
    obtain ⟨rfl, rfl⟩ := Payload.commitment.inj call
    have sameDomain : payload = domain :=
      (EventField.binding.inj (outputEq.symm.trans otherOutput)).2
    subst domain
    change changed.2.RecordsBinding event outputEq _ ∧ _ ∧ _ ∧ _ ∧ _
    exact ⟨⟨pending.2.2.1, pending.2.2.2.1⟩, pending.1, pending.2.1, succeeds,
      pending.2.2.2.2⟩

end Vegas.EventGraphRuntime.BindingMemory
