/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSubmissionFrame

/-! # Mixed binding and waiting before reserved inclusion

The current owner may wait at an early visit, or fix a fresh opaque
commitment. These alternatives use the existing private implementation and
actual response law. Their coupling keeps the entire joint frame before any
inclusion. The public classification of excluded responses remains separate.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- The pending candidate facts required for delayed inclusion follow from
the actual repair response. They are not assumptions about an unobserved value
chosen by the opponent or by an auditor. -/
theorem binding_submission_pending
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh) :
    let app := runtime.reactiveApplication leaks
    let view := repaired.observe app owner
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let changed := memory.repairResponse runtime leaks owner view response
    let left := original.respond app owner response
    let right := repaired.respond app owner changed.1
    left.application.candidates.lookup (owner, .prepared serial) ≠ .fresh ∧
      right.application.candidates.lookup (owner, .prepared serial) ≠ .fresh ∧
      changed.2.actions event = some (cast (congrArg EventField.Action outputEq.symm)
        (left.application.bindingResult (owner, .prepared serial) payload)) ∧
      changed.2.values (.inr event) = some (cast (congrArg EventField.Value outputEq.symm)
        (left.application.bindingResult (owner, .prepared serial) payload)) ∧
      ∀ value, left.application.bindingResult (owner, .prepared serial) payload = .success value →
        right.application.bindingResult (owner, .prepared serial) payload = .success value := by
  let app := runtime.reactiveApplication leaks
  let view := repaired.observe app owner
  let response : app.Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
  let changed := memory.repairResponse runtime leaks owner view response
  let left := original.respond app owner response
  let right := repaired.respond app owner changed.1
  have actualFresh := (frame.slots (.prepared serial)).mp fresh
  have ownFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  have localFresh : view.application.candidates (.prepared serial) = .fresh := actualFresh
  have result : left.application.bindingResult (owner, .prepared serial) payload =
      (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success :=
    runtime.submitted_bindingResult leaks original owner event payload serial opening fresh
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨submitStep_commitment_fixed _ owner event (.prepared serial), ?_, ?_, ?_, ?_⟩
  · cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        change (repaired.respond app owner changed.1).application.candidates.lookup _ ≠ .fresh
        rw [memory.repairResponse_unusable runtime leaks owner view event payload outputEq codeEq
          node serial opening ownFresh actualFresh decoded]
        exact submitStep_commitment_fixed _ owner event (.prepared serial)
    | some value =>
        change (repaired.respond app owner changed.1).application.candidates.lookup _ ≠ .fresh
        rw [memory.repairResponse_usable runtime leaks owner view event payload outputEq codeEq
          node serial opening ownFresh actualFresh value decoded]
        exact submitStep_commitment_fixed _ owner event (.prepared serial)
  · change changed.2.actions event = some (cast (congrArg EventField.Action outputEq.symm)
      (left.application.bindingResult (owner, .prepared serial) payload))
    simp only [changed, repairResponse, response, node, ownFresh, localFresh, and_self,
      ↓reduceIte, result, BindingShadow.rememberCompletion, Function.update_self]
  · change changed.2.values (.inr event) = some (cast (congrArg EventField.Value outputEq.symm)
      (left.application.bindingResult (owner, .prepared serial) payload))
    simp only [changed, repairResponse, response, node, ownFresh, localFresh, and_self,
      ↓reduceIte, result, BindingShadow.rememberCompletion, Function.update_self]
  · intro value same
    change left.application.bindingResult (owner, .prepared serial) payload = .success value at same
    rw [result] at same
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none => simp only [decoded, Option.elim_none] at same; cases same
    | some chosen =>
        simp only [decoded, Option.elim_some, PublicationResult.success.injEq] at same
        subst chosen
        change (repaired.respond app owner changed.1).application.bindingResult _ _ = _
        rw [memory.repairResponse_usable runtime leaks owner view event payload outputEq codeEq
          node serial opening ownFresh actualFresh value decoded]
        rw [runtime.submitted_bindingResult leaks repaired owner event payload serial
          opening actualFresh, decoded, Option.elim_some]

end Vegas.EventGraphRuntime.BindingMemory.Frame
