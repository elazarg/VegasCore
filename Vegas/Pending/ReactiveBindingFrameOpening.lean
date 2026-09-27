/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameStep
import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveHiddenInclusion
import Vegas.Pending.EventBindingInvariant

/-! # Disclosure transitions of the repaired native continuation

An unchanged usable binding has the same authentic certificate on both sides.
Submission and inclusion then preserve the complete repaired frame, including
the owner's reconstructed input and the exact network and receipt history.
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

/-- The native repair invariant itself preserves successful-opening provenance.
No source-state decoder or independence of the initial private values is needed. -/
theorem successful_opening (frame : Frame runtime leaks memory owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    {actor : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding actor payload)) (value : L.Val payload)
    (successful : binding.get? original.application.config.store = some (.success value)) :
    binding.get? repaired.application.config.store = some (.success value) ∧
      ∃ candidate,
        original.application.accepted binding.field = some candidate ∧
        repaired.application.accepted binding.field = some candidate ∧ candidate.1 = actor ∧
        original.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
        repaired.application.candidates.lookup candidate = .openable ⟨payload, value⟩ := by
  have sameValue := Store.BindingRefines.success frame.successful binding value successful
  obtain ⟨candidate, associated, owned, fixed⟩ :=
    leftBinding.success_provenance binding value successful
  obtain ⟨other, rightAssociated, _, rightFixed⟩ :=
    rightBinding.success_provenance binding value sameValue
  have accepted : original.application.accepted = repaired.application.accepted :=
    congrArg PublicView.accepted frame.publicView
  have same : candidate = other := Option.some.inj
    (associated.symm.trans ((congrFun accepted binding.field).trans rightAssociated))
  subst other
  exact ⟨sameValue, candidate, associated, rightAssociated, owned, fixed, rightFixed⟩

/-- An inert application submission is recorded privately using its original
response. Only equality of the actual emitted packet is needed; private request
representations need not agree. -/
theorem inert_submission (frame : Frame runtime leaks memory owner original repaired)
    (left right : WitnessedSubmission graph)
    (leftInert : (runtime.reactiveApplication leaks).submit original.application owner left =
      original.application)
    (rightInert : (runtime.reactiveApplication leaks).submit repaired.application owner right =
      repaired.application)
    (packet : left.emit original.application owner (original.network.known owner) =
      right.emit repaired.application owner (repaired.network.known owner)) :
    let app := runtime.reactiveApplication leaks
    let remembered := memory.record runtime leaks
      (memory.shadow.inputView runtime leaks (repaired.observe app owner))
      ⟨some (.submit left)⟩
    Frame runtime leaks remembered owner
      (original.respond app owner ⟨some (.submit left)⟩)
      (repaired.respond app owner ⟨some (.submit right)⟩) := by
  let app := runtime.reactiveApplication leaks
  have emitted : left.emit (app.submit original.application owner left) owner
      (original.network.known owner) =
      right.emit (app.submit repaired.application owner right) owner
        (repaired.network.known owner) := by rw [leftInert, rightInert]; exact packet
  have nextNetwork :
      (original.respond app owner ⟨some (.submit left)⟩).network =
        (repaired.respond app owner ⟨some (.submit right)⟩).network := by
    change (original.network.submit owner (left.emit
      (app.submit original.application owner left) owner (original.network.known owner))).2 = _
    rw [emitted, frame.network]
    rfl
  have application (execution : app.Execution) (submission : WitnessedSubmission graph)
      (inert : app.submit execution.application owner submission = execution.application) :
      (execution.respond app owner ⟨some (.submit submission)⟩).application =
        execution.application := inert
  refine ⟨memory.restoreRecall_submit runtime leaks original repaired owner left right
    frame.lengths frame.past frame.observed frame.network emitted, ?_, ?_, nextNetwork, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
  · change (⟨(repaired.respond app owner ⟨some (.submit right)⟩).network.observe owner,
      memory.shadow.view (app.observePlayer (app.submit repaired.application owner right) owner),
        repaired.receipts⟩ : app.PlayerView) =
      ⟨(original.respond app owner ⟨some (.submit left)⟩).network.observe owner,
        app.observePlayer (app.submit original.application owner left) owner, original.receipts⟩
    rw [leftInert, rightInert, nextNetwork, frame.receipts]
    exact congrArg (fun view => (⟨
      (repaired.respond app owner ⟨some (.submit right)⟩).network.observe owner,
      view, repaired.receipts⟩ : app.PlayerView))
      (congrArg ReactiveApplication.PlayerView.application frame.observed)
  · simp only [ReactiveApplication.Execution.respond, ↓reduceIte, BindingMemory.record,
      List.length_append, List.length_singleton, frame.lengths]
  · exact frame.service
  · intro who different
    rw [application original left leftInert, application repaired right rightInert]
    exact frame.views who different
  · intro who different
    rw [app.respond_recall_other original owner who different,
      app.respond_recall_other repaired owner who different]
    exact frame.recall who different
  · intro slot
    rw [application original left leftInert, application repaired right rightInert]
    exact frame.slots slot
  · rw [application original left leftInert, application repaired right rightInert]
    exact frame.successful
  · rw [runtime.openingRecall_respond, runtime.openingRecall_respond, frame.openings]
    have calls := congrArg WitnessedPacket.call packet
    change left.call.packet = right.call.packet at calls
    simp only [submittedOpening?, calls]

/-- Accepted application transitions lift to actual inclusion, including the
network update and public receipt. Constructor-specific lemmas establish the
application frame; this lemma adds no assumption about future play. -/
theorem include_accepted (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (packet : WitnessedPacket graph)
    (found : original.network.lookup id = some ⟨id, packet⟩)
    (leftState rightState : State graph)
    (completed : Frame runtime leaks memory owner
      { original with application := leftState } { repaired with application := rightState })
    (leftHandled : handle runtime original.application ⟨id, packet.call⟩ =
      some leftState)
    (rightHandled : handle runtime repaired.application ⟨id, packet.call⟩ =
      some rightState) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  let app := runtime.reactiveApplication leaks
  have rightFound : repaired.network.lookup id = some ⟨id, packet⟩ := frame.network ▸ found
  have nextNetwork : (original.includePending app id).network =
      (repaired.includePending app id).network := by
    rw [app.includePending_network, app.includePending_network]
    rw [frame.network]
  have applyHandler (execution : app.Execution)
      (located : execution.network.lookup id = some ⟨id, packet⟩)
      (after : State graph)
      (handled : handle runtime execution.application ⟨id, packet.call⟩ = some after) :
      (execution.includePending app id).application = after ∧
      (execution.includePending app id).receipts = execution.receipts ++ [⟨id, true⟩] ∧
      (execution.includePending app id).recall = execution.recall := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      located]
    change (handle runtime execution.application ⟨id, packet.call⟩).getD _ = _ ∧
      execution.receipts ++ [(id,
        (handle runtime execution.application ⟨id, packet.call⟩).isSome)] = _ ∧ _
    rw [handled]
    exact ⟨rfl, rfl, trivial⟩
  have leftApplied := applyHandler original found leftState leftHandled
  have rightApplied := applyHandler repaired rightFound rightState rightHandled
  refine ⟨?_, ?_, ?_, nextNetwork, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change memory.restoreRecall runtime leaks ((repaired.includePending app id).recall owner) =
      (original.includePending app id).recall owner
    rw [leftApplied.2.2, rightApplied.2.2]
    exact frame.past
  · change (⟨(repaired.includePending app id).network.observe owner,
      memory.shadow.view (app.observePlayer (repaired.includePending app id).application owner),
        (repaired.includePending app id).receipts⟩ : app.PlayerView) =
      ⟨(original.includePending app id).network.observe owner,
        app.observePlayer (original.includePending app id).application owner,
          (original.includePending app id).receipts⟩
    rw [leftApplied.1, rightApplied.1, leftApplied.2.1, rightApplied.2.1,
      nextNetwork, frame.receipts]
    exact congrArg (fun view => (⟨(repaired.includePending app id).network.observe owner,
      view, repaired.receipts ++ [⟨id, true⟩]⟩ : app.PlayerView))
        (congrArg ReactiveApplication.PlayerView.application completed.observed)
  · change ((repaired.includePending app id).recall owner).length = memory.responses.length
    rw [rightApplied.2.2]
    exact frame.lengths
  · change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
    rw [frame.service, frame.environment]
  · intro who different
    change (original.includePending app id).application.playerView who =
      (repaired.includePending app id).application.playerView who
    rw [leftApplied.1, rightApplied.1]
    exact completed.views who different
  · intro who different
    change (original.includePending app id).recall who =
      (repaired.includePending app id).recall who
    rw [leftApplied.2.2, rightApplied.2.2]
    exact frame.recall who different
  · intro slot
    change (original.includePending app id).application.candidates.lookup (owner, slot) = .fresh ↔
      (repaired.includePending app id).application.candidates.lookup (owner, slot) = .fresh
    rw [leftApplied.1, rightApplied.1]
    exact completed.slots slot
  · change (original.includePending app id).application.config.store.BindingRefines
      (repaired.includePending app id).application.config.store
    rw [leftApplied.1, rightApplied.1]
    exact completed.successful
  · change runtime.openingRecall leaks ((original.includePending app id).recall owner) =
      runtime.openingRecall leaks ((repaired.includePending app id).recall owner)
    rw [leftApplied.2.2, rightApplied.2.2]
    exact frame.openings

/-- A request that discloses an unchanged authentic candidate transmits the
same certificate on the repaired side. Forwarding is included, with identical
actual network knowledge; no certificate is assumed to be owner-exclusive. -/
theorem opening_submission (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (evidence : EvidenceRequest graph)
    (rightFixed : repaired.application.candidates.lookup candidate = .openable raw)
    (certified : (WitnessedSubmission.mk ⟨.opening event candidate raw, none⟩ evidence |>.emit
      original.application owner (original.network.known owner)).evidence =
        some ⟨candidate, raw⟩) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action :=
      ⟨some (.submit ⟨⟨.opening event candidate raw, none⟩, evidence⟩)⟩
    Frame runtime leaks
      (memory.record runtime leaks
        (memory.shadow.inputView runtime leaks (repaired.observe app owner)) response)
      owner (original.respond app owner response) (repaired.respond app owner response) := by
  apply frame.inert_submission _ _ rfl rfl
  have rightCertified :
      (WitnessedSubmission.mk ⟨.opening event candidate raw, none⟩ evidence |>.emit
        repaired.application owner (repaired.network.known owner)).evidence =
          some ⟨candidate, raw⟩ := by
    cases evidence with
    | none => cases certified
    | forward id =>
        change ((repaired.network.known owner).find? _).bind _ = _
        rw [← frame.network]
        exact certified
    | owned fact =>
        simp only [WitnessedSubmission.emit] at certified
        split at certified
        · rename_i available
          cases Option.some.inj certified
          exact WitnessedSubmission.emit_owned _ _ _ _ _ available.1 rightFixed
        · cases certified
  exact congrArg (WitnessedPacket.mk (.opening event candidate raw))
    (certified.trans rightCertified.symm)

/-- A genuine opening of an unchanged binding preserves the entire frame
through actual inclusion. The result is the existing deferred-guard result;
this lemma does not identify application acceptance with successful disclosure. -/
theorem opening_inclusion (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (sender : id.1 = actor) (owned : candidate.1 = actor)
    (associated : original.application.accepted binding.field = some candidate)
    (value : L.Val payload)
    (leftFixed : original.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (rightFixed : repaired.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (leftStored : binding.get? original.application.config.store = some (.success value))
    (rightStored : binding.get? repaired.application.config.store = some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true original.application.config.store =
      some result)
    (evidence : Option (OpeningFact graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.opening event candidate ⟨payload, value⟩, evidence⟩⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  obtain ⟨rightReady, rightTimely, rightAssociated, rightResolved⟩ :=
    opening_right_facts runtime original.application repaired.application frame.publicView
      event actor payload binding checks candidate ready timely associated value leftStored
        rightStored result resolved
  have visible : (graph.outputLayout event).IsPublic := by rw [outputEq]; trivial
  exact frame.include_accepted id _ found _ _
    (frame.complete_unmodified event ready rightReady
      (onlyBindings.public_value_none (.inr event) visible)
      (onlyBindings.public_action_none event visible) _ _)
    (handle_opening_eq runtime original.application id event candidate actor payload binding checks
      outputEq codeEq node ready timely sender owned associated value leftFixed leftStored result
        resolved)
    (handle_opening_eq runtime repaired.application id event candidate actor payload binding checks
      outputEq codeEq node rightReady rightTimely sender owned rightAssociated value rightFixed
        rightStored result rightResolved)

end Vegas.EventGraphRuntime.BindingMemory.Frame
