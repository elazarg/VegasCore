module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingCoupling
public import Vegas.EventGraph.BindingRefinement
public import Vegas.Pending.ReactiveSubmissionRecall

@[expose] public section

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
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

structure Frame (memory : BindingMemory timeouts leaks) (owner : Player)
    (original repaired : ((reactiveApplication timeouts) leaks).Execution) : Prop where
  past : memory.restoreRecall timeouts leaks (repaired.logs owner) = original.logs owner
  observed : memory.shadow.inputView timeouts leaks
    (repaired.observe ((reactiveApplication timeouts) leaks) owner) =
      original.observe ((reactiveApplication timeouts) leaks) owner
  lengths : (repaired.logs owner).length = memory.responses.length
  network : original.network = repaired.network
  service : original.environmentRecall = repaired.environmentRecall
  views : ∀ who, who ≠ owner →
    original.application.playerView who = repaired.application.playerView who
  logs : ∀ who, who ≠ owner → original.logs who = repaired.logs who
  slots : ∀ query, original.application.candidates.lookup (owner, query) = .fresh ↔
    repaired.application.candidates.lookup (owner, query) = .fresh
  successful : original.application.config.store.BindingRefines repaired.application.config.store
  submissions : (submissionRecall timeouts) leaks (original.logs owner) =
    (submissionRecall timeouts) leaks (repaired.logs owner)

theorem frame_atRecall (owner : Player)
    (execution : ((reactiveApplication timeouts) leaks).Execution) :
    Frame timeouts leaks (atRecall timeouts leaks (execution.logs owner)) owner
      execution execution where
  past := restoreRecall_atRecall timeouts leaks _
  observed := BindingShadow.inputView_empty timeouts leaks _
  lengths := by simp only [atRecall, List.length_map]
  network := rfl
  service := rfl
  views := fun _ _ => rfl
  logs := fun _ _ => rfl
  slots := fun _ => Iff.rfl
  successful := Store.BindingRefines.refl _
  submissions := rfl

namespace Frame

variable {timeouts leaks} {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : ((reactiveApplication timeouts) leaks).Execution}

theorem receipts (frame : Frame timeouts leaks memory owner original repaired) :
    original.receipts = repaired.receipts :=
  (congrArg ReactiveApplication.PlayerView.receipts frame.observed).symm

theorem publicView (frame : Frame timeouts leaks memory owner original repaired) :
    original.application.publicView = repaired.application.publicView :=
  (congrArg (fun view : ((reactiveApplication timeouts) leaks).PlayerView =>
    view.application.publicView) frame.observed).symm

theorem firstSubmission (frame : Frame timeouts leaks memory owner original repaired)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    (firstSubmission timeouts) leaks (original.logs owner) response =
      (firstSubmission timeouts) leaks (repaired.logs owner) response := by
  unfold EventGraphRuntime.firstSubmission
  cases (submittedEvent? timeouts) leaks response with
  | none => rfl
  | some event =>
      exact congrArg Bool.not ((eventRecorded_congr timeouts) leaks _ _ frame.submissions event)

theorem environment (frame : Frame timeouts leaks memory owner original repaired) :
    original.observeEnvironment ((reactiveApplication timeouts) leaks) =
      repaired.observeEnvironment ((reactiveApplication timeouts) leaks) := by
  change (⟨original.network.publicView, original.application.publicView,
    original.receipts⟩ : ((reactiveApplication timeouts) leaks).EnvironmentView) =
      ⟨repaired.network.publicView, repaired.application.publicView, repaired.receipts⟩
  rw [frame.network, frame.receipts, frame.publicView]

/-- A passive sample is shared on the equal pending pool. The sampled set is
not restricted, including when the activated player is the repaired owner. -/
theorem activate (frame : Frame timeouts leaks memory owner original repaired)
    (actor : Player) (selected : Finset (MessageId Player)) :
    let app := (reactiveApplication timeouts) leaks
    Frame timeouts leaks memory owner
      { original with
        network := original.network.learn actor selected
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment app, .activate actor⟩] }
      { repaired with
        network := repaired.network.learn actor selected
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment app, .activate actor⟩] } := by
  refine ⟨frame.past, ?_, frame.lengths, ?_, ?_, frame.views, frame.logs, frame.slots,
    frame.successful, frame.submissions⟩
  · have ownApplication := congrArg ReactiveApplication.PlayerView.application frame.observed
    change (⟨(repaired.network.learn actor selected).observe owner,
      memory.shadow.view (((reactiveApplication timeouts) leaks).observePlayer
        repaired.application owner), repaired.receipts⟩ :
          ((reactiveApplication timeouts) leaks).PlayerView) =
      ⟨(original.network.learn actor selected).observe owner,
        ((reactiveApplication timeouts) leaks).observePlayer original.application owner,
          original.receipts⟩
    rw [frame.network, frame.receipts]
    exact congrArg (fun view => (⟨(repaired.network.learn actor selected).observe owner,
      view, repaired.receipts⟩ : ((reactiveApplication timeouts) leaks).PlayerView)) ownApplication
  · rw [frame.network]
  · rw [frame.service, frame.environment]

private theorem foreign_catalog (execution : ((reactiveApplication timeouts) leaks).Execution)
    (actor : Player) (different : owner ≠ actor)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    (fun query => (execution.respond ((reactiveApplication timeouts) leaks)
      actor response).application.candidates.lookup (owner, query)) =
        fun query => execution.application.candidates.lookup (owner, query) := by
  have same : (execution.respond ((reactiveApplication timeouts) leaks)
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
theorem foreign_response (frame : Frame timeouts leaks memory owner original repaired)
    (actor : Player) (foreign : actor ≠ owner)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    Frame timeouts leaks memory owner
      (original.respond ((reactiveApplication timeouts) leaks) actor response)
      (repaired.respond ((reactiveApplication timeouts) leaks) actor response) := by
  let app := (reactiveApplication timeouts) leaks
  have paired := memory.foreign_response timeouts leaks original repaired owner actor foreign
    frame.past frame.observed frame.network frame.views frame.logs response
  refine ⟨paired.1, paired.2.1, ?_, paired.2.2.1, ?_, paired.2.2.2.2.1,
    paired.2.2.2.2.2, ?_, ?_, ?_⟩
  · rw [app.respond_recall_other repaired actor owner foreign.symm response]
    exact frame.lengths
  · exact frame.service
  · intro query
    rw [congrFun (foreign_catalog original actor foreign.symm response) query,
      congrFun (foreign_catalog repaired actor foreign.symm response) query]
    exact frame.slots query
  · rw [((reactive_respond_application timeouts) leaks original actor response).1,
      ((reactive_respond_application timeouts) leaks repaired actor response).1]
    exact frame.successful
  · rw [app.respond_recall_other original actor owner foreign.symm response,
      app.respond_recall_other repaired actor owner foreign.symm response]
    exact frame.submissions

/-- Silence preserves the concrete frame while recording the
original response in private memory. No pending observation is discarded. -/
theorem transport_response (frame : Frame timeouts leaks memory owner original repaired)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (notSubmitted : ∀ submission, response.transmission ≠ some submission) :
    let app := (reactiveApplication timeouts) leaks
    let remembered := memory.record timeouts leaks
      (memory.shadow.inputView timeouts leaks (repaired.observe app owner)) response
    Frame timeouts leaks remembered owner (original.respond app owner response)
      (repaired.respond app owner response) := by
  let app := (reactiveApplication timeouts) leaks
  have paired := memory.transport_response timeouts leaks original repaired owner frame.lengths
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
    exact frame.logs who different
  · intro query
    rw [unchanged original, unchanged repaired]
    exact frame.slots query
  · rw [unchanged original, unchanged repaired]
    exact frame.successful
  · rw [(submissionRecall_respond timeouts), (submissionRecall_respond timeouts), frame.submissions]

end Frame
end Vegas.EventGraphRuntime.BindingMemory
