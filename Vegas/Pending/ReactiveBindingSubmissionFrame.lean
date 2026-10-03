/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrame

/-! # Binding repair before delayed inclusion

The private repair preserves the joint execution frame as soon as the opaque
packet is submitted. Inclusion need not immediately follow the owner's response:
the existing activation and response lemmas can therefore carry the frame
through an arbitrary intervening roster, including passive pending-message reads.
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

/-- Private unusability is repaired at transmission. The original raw material
is recorded locally, while every opponent's entire input and the public packet
remain the same jointly. No receipt or inclusion is presumed. -/
theorem binding_submission
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (ready : original.application.config.cut.Ready event) :
    let app := runtime.reactiveApplication leaks
    let view := repaired.observe app owner
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let change := memory.repairResponse runtime leaks owner view response
    let remembered : BindingMemory runtime leaks :=
      ⟨change.2, memory.responses ++ [(memory.shadow.inputView runtime leaks view, response)]⟩
    Frame runtime leaks remembered owner
      (original.respond app owner response) (repaired.respond app owner change.1) := by
  let app := runtime.reactiveApplication leaks
  let view := repaired.observe app owner
  let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
    | none => some (⟨payload, L.someValue payload⟩ : Raw L)
    | some _ => opening
  let response : app.Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
  let change := memory.repairResponse runtime leaks owner view response
  let remembered : BindingMemory runtime leaks :=
    ⟨change.2, memory.responses ++ [(memory.shadow.inputView runtime leaks view, response)]⟩
  let left := original.respond app owner response
  let right := repaired.respond app owner change.1
  have actualFresh := (frame.slots (.prepared serial)).mp fresh
  have ownFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  have rightReady : repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
    exact ready
  have changed : change.1 =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacementOpening⟩, .none⟩⟩ := by
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        rw [memory.repairResponse_unusable runtime leaks owner view event payload outputEq codeEq
          node serial opening ownFresh actualFresh decoded]
        simp only [replacementOpening, decoded]
        rfl
    | some value =>
        rw [congrArg Prod.fst (memory.repairResponse_usable runtime leaks owner view event payload
          outputEq codeEq node serial opening ownFresh actualFresh value decoded)]
        simp only [replacementOpening, decoded]
  have restored := memory.repairResponse_submit_input runtime leaks owner original repaired
    frame.lengths frame.past frame.observed frame.network event payload outputEq codeEq node
      serial opening fresh actualFresh rightReady
  change remembered.restoreRecall runtime leaks (right.recall owner) = left.recall owner ∧
    remembered.shadow.inputView runtime leaks (right.observe app owner) =
      left.observe app owner ∧ (right.recall owner).length = remembered.responses.length at restored
  have paired := runtime.rawBinding_submit_hidden_congr leaks original repaired owner
    frame.network frame.receipts frame.publicView frame.views frame.recall event serial
      opening replacementOpening
  have physical : right = repaired.respond app owner
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacementOpening⟩, .none⟩⟩ := by
    dsimp only [right]
    rw [changed]
  change left.network = _ ∧ left.receipts = _ ∧ left.application.publicView = _ ∧
    (∀ who, who ≠ owner → left.application.playerView who = _) ∧
    (∀ who, who ≠ owner → left.recall who = _) at paired
  rw [← physical] at paired
  change Frame runtime leaks remembered owner left right
  refine ⟨restored.1, restored.2.1, restored.2.2, paired.1, frame.service,
    paired.2.2.2.1, paired.2.2.2.2, ?_, ?_, ?_⟩
  · intro query
    dsimp only [left, right]
    rw [changed]
    exact (runtime.submitted_binding_fresh_iff leaks original owner event serial
      opening query).trans
      ((and_congr Iff.rfl (frame.slots query)).trans
        (runtime.submitted_binding_fresh_iff leaks repaired owner event serial
          replacementOpening query).symm)
  · change left.application.config.store.BindingRefines right.application.config.store
    rw [(runtime.reactive_respond_application leaks original owner response).1,
      (runtime.reactive_respond_application leaks repaired owner change.1).1]
    exact frame.successful
  · change runtime.submissionRecall leaks ((original.respond app owner response).recall owner) =
      runtime.submissionRecall leaks ((repaired.respond app owner change.1).recall owner)
    rw [runtime.submissionRecall_respond, runtime.submissionRecall_respond,
      frame.submissions, changed]
    rfl

/-- Delayed inclusion consumes the same pending opaque envelope after any
intervening response window. The remembered original typed result is local
implementation memory; the successful-value premise is the actual candidate
fact established by the repair and preserved until this inclusion. -/
theorem pending_binding_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph)
    (sender : id.1 = owner) (owned : candidate.1 = owner)
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (vacant : original.application.accepted (.inr event) = none)
    (unused : original.application.HandleUnused candidate)
    (leftFixed : original.application.candidates.lookup candidate ≠ .fresh)
    (rightFixed : repaired.application.candidates.lookup candidate ≠ .fresh)
    (rememberedAction : memory.shadow.actions event = some
      (cast (congrArg EventField.Action outputEq.symm)
        (original.application.bindingResult candidate payload)))
    (rememberedValue : memory.shadow.values (.inr event) = some
      (cast (congrArg EventField.Value outputEq.symm)
        (original.application.bindingResult candidate payload)))
    (successful : ∀ value, original.application.bindingResult candidate payload = .success value →
      repaired.application.bindingResult candidate payload = .success value) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  let app := runtime.reactiveApplication leaks
  have paired := runtime.reactive_include_binding_hidden_congr leaks original repaired owner
    frame.network frame.receipts frame.publicView frame.views frame.recall id event candidate
      none found
  have own := memory.shadow.include_binding_input runtime leaks original repaired owner
    frame.observed frame.network event payload outputEq codeEq node id candidate sender owned
      found ready timely vacant unused leftFixed rightFixed
        (Or.inl ⟨rememberedAction, rememberedValue⟩)
  have recall (execution : app.Execution) :
      (execution.includePending app id).recall = execution.recall := by
    simp only [ReactiveApplication.Execution.includePending]
    split <;> rfl
  have foundRight : repaired.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩ := frame.network ▸ found
  refine ⟨?_, own, ?_, paired.1, ?_, paired.2.2.1, paired.2.2.2, ?_, ?_, ?_⟩
  · change memory.restoreRecall runtime leaks
      ((repaired.includePending app id).recall owner) =
        (original.includePending app id).recall owner
    rw [recall original, recall repaired]
    exact frame.past
  · change ((repaired.includePending app id).recall owner).length = memory.responses.length
    rw [recall repaired]
    exact frame.lengths
  · rw [frame.service, frame.environment]
  · intro query
    change (original.includePending app id).application.candidates.lookup (owner, query) = .fresh ↔
      (repaired.includePending app id).application.candidates.lookup (owner, query) = .fresh
    rw [runtime.reactive_include_fixed_binding_candidates leaks original id event candidate
      none found leftFixed, runtime.reactive_include_fixed_binding_candidates leaks repaired
      id event candidate none foundRight rightFixed]
    exact frame.slots query
  · have rightReady : repaired.application.config.cut.Ready event := by
      rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
      exact ready
    have rightTimely : repaired.application.WithinDeadline runtime event := by
      unfold State.WithinDeadline
      rw [← show original.application.clock = repaired.application.clock from
        congrArg PublicView.clock frame.publicView,
        ← show original.application.activatedAt = repaired.application.activatedAt from
          congrArg PublicView.activatedAt frame.publicView]
      exact timely
    have associated : original.application.accepted = repaired.application.accepted :=
      congrArg PublicView.accepted frame.publicView
    have rightVacant : repaired.application.accepted (.inr event) = none := by
      rw [← associated]
      exact vacant
    have rightUnused : repaired.application.HandleUnused candidate := by
      intro field accepted
      exact unused field ((congrFun associated field).trans accepted)
    have handled := runtime.handle_commitment_eq original.application id event candidate owner
      payload outputEq codeEq node ready timely sender owned vacant unused
    have handledRight := runtime.handle_commitment_eq repaired.application id event candidate owner
      payload outputEq codeEq node rightReady rightTimely sender owned rightVacant rightUnused
    change (original.includePending app id).application.config.store.BindingRefines
      (repaired.includePending app id).application.config.store
    simp only [app, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, foundRight, reactiveApplication_handle, WitnessedPacket.tokenValid_commitment,
      ite_true, handled, handledRight, Option.getD_some, State.complete]
    apply Config.bindingRefines_complete frame.successful event ready rightReady
    apply EventField.BindingRefines.cast_some outputEq.symm
    intro value equal
    exact congrArg some (successful value (Option.some.inj equal))
  · change runtime.submissionRecall leaks ((original.includePending app id).recall owner) =
      runtime.submissionRecall leaks ((repaired.includePending app id).recall owner)
    rw [recall original, recall repaired]
    exact frame.submissions

end Vegas.EventGraphRuntime.BindingMemory.Frame
