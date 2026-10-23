/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRevealBlock
import Vegas.Pending.ReactiveBindingCoupling
import Vegas.Pending.ReactiveRawBindingFrame
import Vegas.EventGraph.BindingRefinement
import Vegas.Pending.ReactiveSubmissionRecall

/-! # The concrete frame carried by a repaired native continuation

The relation pairs two existing executions and the repaired player's private
implementation memory. It preserves the complete joint observations of the
other players, network and service, and reconstructs the original player's
input. It is a proof invariant, not additional runtime state or an observer.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

structure Frame (memory : BindingMemory runtime leaks) (owner : Player)
    (original repaired : (runtime.reactiveApplication leaks).Execution) : Prop where
  past : memory.restoreRecall runtime leaks (repaired.recall owner) = original.recall owner
  observed : memory.shadow.inputView runtime leaks
    (repaired.observe (runtime.reactiveApplication leaks) owner) =
      original.observe (runtime.reactiveApplication leaks) owner
  lengths : (repaired.recall owner).length = memory.responses.length
  network : original.network = repaired.network
  service : original.environmentRecall = repaired.environmentRecall
  views : ∀ who, who ≠ owner →
    original.application.playerView who = repaired.application.playerView who
  recall : ∀ who, who ≠ owner → original.recall who = repaired.recall who
  slots : ∀ query, original.application.candidates.lookup (owner, query) = .fresh ↔
    repaired.application.candidates.lookup (owner, query) = .fresh
  successful : original.application.config.store.BindingRefines repaired.application.config.store
  submissions : runtime.submissionRecall leaks (original.recall owner) =
    runtime.submissionRecall leaks (repaired.recall owner)

theorem frame_atRecall (owner : Player)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    Frame runtime leaks (atRecall runtime leaks (execution.recall owner)) owner
      execution execution where
  past := restoreRecall_atRecall runtime leaks _
  observed := BindingShadow.inputView_empty runtime leaks _
  lengths := by simp only [atRecall, List.length_map]
  network := rfl
  service := rfl
  views := fun _ _ => rfl
  recall := fun _ _ => rfl
  slots := fun _ => Iff.rfl
  successful := Store.BindingRefines.refl _
  submissions := rfl

namespace Frame

variable {runtime leaks} {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

theorem receipts (frame : Frame runtime leaks memory owner original repaired) :
    original.receipts = repaired.receipts :=
  (congrArg ReactiveApplication.PlayerView.receipts frame.observed).symm

theorem publicView (frame : Frame runtime leaks memory owner original repaired) :
    original.application.publicView = repaired.application.publicView :=
  (congrArg (fun view : (runtime.reactiveApplication leaks).PlayerView =>
    view.application.publicView) frame.observed).symm

theorem firstSubmission (frame : Frame runtime leaks memory owner original repaired)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.firstSubmission leaks (original.recall owner) response =
      runtime.firstSubmission leaks (repaired.recall owner) response := by
  unfold EventGraphRuntime.firstSubmission
  cases runtime.submittedEvent? leaks response with
  | none => rfl
  | some event =>
      exact congrArg Bool.not (runtime.eventRecorded_congr leaks _ _ frame.submissions event)

theorem environment (frame : Frame runtime leaks memory owner original repaired) :
    original.observeEnvironment (runtime.reactiveApplication leaks) =
      repaired.observeEnvironment (runtime.reactiveApplication leaks) := by
  change (⟨original.network.publicView, original.application.publicView,
    original.receipts⟩ : (runtime.reactiveApplication leaks).EnvironmentView) =
      ⟨repaired.network.publicView, repaired.application.publicView, repaired.receipts⟩
  rw [frame.network, frame.receipts, frame.publicView]

/-- A passive sample is shared on the equal pending pool. The sampled set is
not restricted, including when the activated player is the repaired owner. -/
theorem activate (frame : Frame runtime leaks memory owner original repaired)
    (actor : Player) (selected : Finset (MessageId Player)) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original with
        network := original.network.learn actor selected
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment app, .activate actor⟩] }
      { repaired with
        network := repaired.network.learn actor selected
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment app, .activate actor⟩] } := by
  refine ⟨frame.past, ?_, frame.lengths, ?_, ?_, frame.views, frame.recall, frame.slots,
    frame.successful, frame.submissions⟩
  · have ownApplication := congrArg ReactiveApplication.PlayerView.application frame.observed
    change (⟨(repaired.network.learn actor selected).observe owner,
      memory.shadow.view ((runtime.reactiveApplication leaks).observePlayer
        repaired.application owner), repaired.receipts⟩ :
          (runtime.reactiveApplication leaks).PlayerView) =
      ⟨(original.network.learn actor selected).observe owner,
        (runtime.reactiveApplication leaks).observePlayer original.application owner,
          original.receipts⟩
    rw [frame.network, frame.receipts]
    exact congrArg (fun view => (⟨(repaired.network.learn actor selected).observe owner,
      view, repaired.receipts⟩ : (runtime.reactiveApplication leaks).PlayerView)) ownApplication
  · rw [frame.network]
  · rw [frame.service, frame.environment]

private theorem foreign_catalog (execution : (runtime.reactiveApplication leaks).Execution)
    (actor : Player) (different : owner ≠ actor)
    (response : (runtime.reactiveApplication leaks).Action) :
    (fun query => (execution.respond (runtime.reactiveApplication leaks)
      actor response).application.candidates.lookup (owner, query)) =
        fun query => execution.application.candidates.lookup (owner, query) := by
  have same : (execution.respond (runtime.reactiveApplication leaks)
      actor response).application.playerView owner = execution.application.playerView owner := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        exact (submitStep_playerView_other (material.call.register execution.application actor)
          actor owner different material.call.packet).trans
            (material.call.register_other execution.application actor owner different)
  exact congrArg PlayerView.candidates same

/-- Arbitrary foreign raw responses, including forwarding and local evidence
aliases, preserve the repaired player's input and the joint outside frame. -/
theorem foreign_response (frame : Frame runtime leaks memory owner original repaired)
    (actor : Player) (foreign : actor ≠ owner)
    (response : (runtime.reactiveApplication leaks).Action) :
    Frame runtime leaks memory owner
      (original.respond (runtime.reactiveApplication leaks) actor response)
      (repaired.respond (runtime.reactiveApplication leaks) actor response) := by
  let app := runtime.reactiveApplication leaks
  have paired := memory.foreign_response runtime leaks original repaired owner actor foreign
    frame.past frame.observed frame.network frame.views frame.recall response
  refine ⟨paired.1, paired.2.1, ?_, paired.2.2.1, ?_, paired.2.2.2.2.1,
    paired.2.2.2.2.2, ?_, ?_, ?_⟩
  · rw [app.respond_recall_other repaired actor owner foreign.symm response]
    exact frame.lengths
  · exact frame.service
  · intro query
    rw [congrFun (foreign_catalog original actor foreign.symm response) query,
      congrFun (foreign_catalog repaired actor foreign.symm response) query]
    exact frame.slots query
  · rw [(runtime.reactive_respond_application leaks original actor response).1,
      (runtime.reactive_respond_application leaks repaired actor response).1]
    exact frame.successful
  · rw [app.respond_recall_other original actor owner foreign.symm response,
      app.respond_recall_other repaired actor owner foreign.symm response]
    exact frame.submissions

/-- Silence preserves the concrete frame while recording the
original response in private memory. No pending observation is discarded. -/
theorem transport_response (frame : Frame runtime leaks memory owner original repaired)
    (response : (runtime.reactiveApplication leaks).Action)
    (notSubmitted : ∀ submission, response.transmission ≠ some submission) :
    let app := runtime.reactiveApplication leaks
    let remembered := memory.record runtime leaks
      (memory.shadow.inputView runtime leaks (repaired.observe app owner)) response
    Frame runtime leaks remembered owner (original.respond app owner response)
      (repaired.respond app owner response) := by
  let app := runtime.reactiveApplication leaks
  have paired := memory.transport_response runtime leaks original repaired owner frame.lengths
    frame.past frame.observed response notSubmitted
  have unchanged (execution : app.Execution) :
      (execution.respond app owner response).application = execution.application := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some submission => exact (notSubmitted submission rfl).elim
  refine ⟨paired.1, paired.2.1, paired.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact frame.network
    | some submission => exact (notSubmitted submission rfl).elim
  · rw [app.respond_environmentRecall, app.respond_environmentRecall]
    exact frame.service
  · intro who different
    rw [unchanged original, unchanged repaired]
    exact frame.views who different
  · intro who different
    rw [app.respond_recall_other original owner who different response,
      app.respond_recall_other repaired owner who different response]
    exact frame.recall who different
  · intro query
    rw [unchanged original, unchanged repaired]
    exact frame.slots query
  · rw [unchanged original, unchanged repaired]
    exact frame.successful
  · rw [runtime.submissionRecall_respond, runtime.submissionRecall_respond, frame.submissions]

end Frame
end Vegas.EventGraphRuntime.BindingMemory
