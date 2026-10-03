/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrame
import Vegas.Pending.ReactiveBindingCertificateRepair

/-! # Copying a later bare commitment with its actual candidate meaning

A copied response records only the candidate update computed from the owner's
reconstructed input. The raw material is never decoded as the addressed node's
payload. Fresh mistyped material therefore retains its real certificate
capability; missing material fixes an unopenable candidate on both sides. Reused fixed
slots retain their existing meanings rather than being registered again.

This is an actual response-frame law. It neither changes the private repair
implementation nor proves retained-menu admission or continuation domination.
Inclusion of a reused changed candidate remains a separate obligation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A new owned registration is described by the actual input and chosen
bare response. Missing and mistyped raw material retain their actual meanings;
the addressed node need not be a binding. -/
def FreshOwnedBindingResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (view : ReactivePlayerView graph)
    (response : (runtime.reactiveApplication leaks).Action) : Prop :=
  ∃ (event : graph.EventId) (serial : Nat) (opening : Option (Raw L)),
    view.candidates (.prepared serial) = .fresh ∧
      response = ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩

namespace BindingMemory.Frame

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Copying a bare owned commitment preserves the entire response frame after
recording its actual candidate meaning. No fresh-slot or typed-value premise is
needed for this response transition; completion memory is unchanged. -/
theorem copied_binding_submission
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L)) :
    let app := runtime.reactiveApplication leaks
    let input := memory.shadow.inputView runtime leaks (repaired.observe app owner)
    let call : Submission graph := ⟨.commitment event (owner, .prepared serial), opening⟩
    let response : app.Action := ⟨some ⟨call, .none⟩⟩
    let remembered : BindingMemory runtime leaks :=
      ⟨memory.shadow.rememberCandidate (.prepared serial)
        (call.candidateAfter owner input.application.candidates (.prepared serial)),
        memory.responses ++ [(input, response)]⟩
    let left := original.respond app owner response
    let right := repaired.respond app owner response
    Frame runtime leaks remembered owner left right ∧
      remembered.shadow.OwnBindings owner ∧
      remembered.shadow.CompletedAt left.application.config := by
  intro app input call response remembered left right
  have paired := runtime.rawBinding_submit_hidden_congr leaks original repaired owner
    frame.network frame.receipts frame.publicView frame.views frame.recall event serial
      opening opening
  change left.network = right.network ∧ left.receipts = right.receipts ∧
    left.application.publicView = right.application.publicView ∧
    (∀ who, who ≠ owner → left.application.playerView who = right.application.playerView who) ∧
    (∀ who, who ≠ owner → left.recall who = right.recall who) at paired
  have packet : (⟨call, .none⟩ : WitnessedSubmission graph).emit
      (app.submit original.application owner ⟨call, .none⟩) owner
        (original.network.known owner) =
      (⟨call, .none⟩ : WitnessedSubmission graph).emit
        (app.submit repaired.application owner ⟨call, .none⟩) owner
          (repaired.network.known owner) := by
    change WitnessedPacket.mk call.packet none
        ((app.submit original.application owner ⟨call, .none⟩).publicView.tokenFor call.packet) =
      WitnessedPacket.mk call.packet none
        ((app.submit repaired.application owner ⟨call, .none⟩).publicView.tokenFor call.packet)
    rw [reactiveApplication_submit_publicView, reactiveApplication_submit_publicView,
      frame.publicView]
  have restored := memory.restoreRecall_submit runtime leaks original repaired owner
    ⟨call, .none⟩ ⟨call, .none⟩ frame.lengths frame.past frame.observed frame.network packet
  have catalogue := memory.shadow.rememberCandidate_submit_view runtime leaks
    original.application repaired.application owner
      (congrArg ReactiveApplication.PlayerView.application frame.observed) event serial
        opening opening
  change remembered.shadow.view (app.observePlayer right.application owner) =
    app.observePlayer left.application owner at catalogue
  refine ⟨?_, onlyBindings.rememberCandidate _ _, ?_⟩
  · refine ⟨restored, ?_, ?_, paired.1, frame.service, paired.2.2.2.1, paired.2.2.2.2,
      ?_, ?_, ?_⟩
    · change (⟨right.network.observe owner,
        remembered.shadow.view (app.observePlayer right.application owner), right.receipts⟩ :
          app.PlayerView) =
        ⟨left.network.observe owner, app.observePlayer left.application owner, left.receipts⟩
      rw [catalogue, ← paired.1, ← paired.2.1]
    · change (right.recall owner).length = remembered.responses.length
      simp only [right, remembered, ReactiveApplication.Execution.respond, ↓reduceIte,
        List.length_append, List.length_singleton, frame.lengths]
    · intro query
      exact (runtime.submitted_binding_fresh_iff leaks original owner event serial opening
        query).trans ((and_congr Iff.rfl (frame.slots query)).trans
          (runtime.submitted_binding_fresh_iff leaks repaired owner event serial opening
            query).symm)
    · change left.application.config.store.BindingRefines right.application.config.store
      rw [(runtime.reactive_respond_application leaks original owner response).1,
        (runtime.reactive_respond_application leaks repaired owner response).1]
      exact frame.successful
    · change runtime.submissionRecall leaks ((original.respond app owner response).recall owner) =
        runtime.submissionRecall leaks ((repaired.respond app owner response).recall owner)
      rw [runtime.submissionRecall_respond, runtime.submissionRecall_respond, frame.submissions]
  · change (memory.shadow.rememberCandidate _ _).CompletedAt left.application.config
    rw [(runtime.reactive_respond_application leaks original owner response).1]
    exact past.rememberCandidate _ _

/-- Fresh copied material acquires the same fixed meaning on both executions,
including mistyped and missing material. The addressed payload is irrelevant. -/
theorem copied_binding_fresh_meaning
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let left := (original.respond app owner response).application.candidates.lookup
      (owner, .prepared serial)
    let right := (repaired.respond app owner response).application.candidates.lookup
      (owner, .prepared serial)
    left ≠ .fresh ∧ left = right ∧
      left = opening.elim .unopenable CommitmentCandidate.openable := by
  intro app response left right
  have rightFresh := (frame.slots (.prepared serial)).mp fresh
  let call : Submission graph := ⟨.commitment event (owner, .prepared serial), opening⟩
  change (submitStep (call.register original.application owner) owner call.packet).candidates.lookup
      (owner, .prepared serial) ≠ .fresh ∧
    (submitStep (call.register original.application owner) owner call.packet).candidates.lookup
        (owner, .prepared serial) =
      (submitStep (call.register repaired.application owner) owner call.packet).candidates.lookup
        (owner, .prepared serial) ∧
    (submitStep (call.register original.application owner) owner call.packet).candidates.lookup
      (owner, .prepared serial) = opening.elim .unopenable CommitmentCandidate.openable
  simp only [call.candidateAfter_eq]
  cases opening <;> simp only [call, Submission.candidateAfter, fresh, rightFresh, and_self,
    ↓reduceIte, Option.elim_none, Option.elim_some] <;> simp

end BindingMemory.Frame

end Vegas.EventGraphRuntime
