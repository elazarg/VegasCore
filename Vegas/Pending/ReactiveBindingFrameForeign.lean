/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameOpening

/-! # Other players' accepted commitments during a private repair

Their actual catalogs, inputs and responses agree. The same candidate can
therefore be associated with the next binding on both sides, without erasing
the repaired player's unrelated private binding differences.
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

theorem setAccepted (frame : Frame runtime leaks memory owner original repaired)
    (accepted : graph.Field → Option (Handle graph)) :
    Frame runtime leaks memory owner
      { original with application := { original.application with accepted := accepted } }
      { repaired with application := { repaired.application with accepted := accepted } } := by
  let app := runtime.reactiveApplication leaks
  refine ⟨frame.past, ?_, frame.lengths, frame.network, frame.service, ?_,
    frame.recall, frame.slots⟩
  · have application := congrArg ReactiveApplication.PlayerView.application frame.observed
    have changed := congrArg (fun view : ReactivePlayerView graph =>
      { view with publicView := { view.publicView with accepted := accepted } }) application
    change (⟨repaired.network.observe owner,
      memory.shadow.view (app.observePlayer { repaired.application with accepted := accepted }
        owner), repaired.receipts⟩ : app.PlayerView) =
      ⟨original.network.observe owner,
        app.observePlayer { original.application with accepted := accepted } owner,
          original.receipts⟩
    rw [frame.network, frame.receipts]
    exact congrArg (fun view => (⟨repaired.network.observe owner, view,
      repaired.receipts⟩ : app.PlayerView)) changed
  · intro actor different
    exact congrArg (fun view : PlayerView graph =>
      { view with publicView := { view.publicView with accepted := accepted } })
        (frame.views actor different)

/-- Reserved inclusion of another player's fixed canonical candidate retains
the complete frame, for successful or failed private material. -/
theorem foreign_binding_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (past : memory.shadow.CompletedAt original.application.config)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (actor : Player) (different : actor ≠ owner) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind actor payload)
    (node : nodeView graph event = .bind actor payload outputEq codeEq)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (sender : id.1 = actor) (owned : candidate.1 = actor)
    (vacant : original.application.accepted (.inr event) = none)
    (unused : original.application.HandleUnused candidate)
    (fixed : original.application.candidates.lookup candidate ≠ .fresh)
    (evidence : Option (OpeningFact graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence⟩⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  have rightReady : repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
    exact ready
  have clocks : original.application.clock = repaired.application.clock :=
    congrArg PublicView.clock frame.publicView
  have activations : original.application.activatedAt = repaired.application.activatedAt :=
    congrArg PublicView.activatedAt frame.publicView
  have accepted : original.application.accepted = repaired.application.accepted :=
    congrArg PublicView.accepted frame.publicView
  have rightTimely : repaired.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    rwa [← clocks, ← activations]
  have rightVacant : repaired.application.accepted (.inr event) = none := by
    rw [← accepted]
    exact vacant
  have rightUnused : repaired.application.HandleUnused candidate := by
    intro field associated
    exact unused field ((congrFun accepted field).trans associated)
  have candidates : original.application.candidates.lookup candidate =
      repaired.application.candidates.lookup candidate := by
    have observed := congrArg PlayerView.candidates (frame.views actor different)
    have handleEq : candidate = (actor, candidate.2) := by
      exact Prod.ext owned rfl
    rw [handleEq]
    exact congrFun observed candidate.2
  have rightFixed : repaired.application.candidates.lookup candidate ≠ .fresh :=
    candidates ▸ fixed
  have sameResult : repaired.application.bindingResult candidate payload =
      original.application.bindingResult candidate payload := by
    unfold State.bindingResult
    rw [candidates]
  let action : graph.Action event := cast (congrArg EventField.Action outputEq.symm)
    (original.application.bindingResult candidate payload)
  let value : (graph.outputLayout event).Value := cast (congrArg EventField.Value outputEq.symm)
    (original.application.bindingResult candidate payload)
  let association := Function.update original.application.accepted (.inr event) (some candidate)
  have completed := frame.complete_unmodified event ready rightReady
    (past.ready_none event ready).2 (past.ready_none event ready).1 action value
  have paired := completed.setAccepted association
  apply frame.include_accepted id _ found _ _ paired
  · rw [handle_commitment_eq runtime original.application id event candidate actor payload outputEq
      codeEq node ready timely sender owned vacant unused,
        original.application.candidates.freeze_eq_self_of_not_fresh candidate fixed]
    rfl
  · rw [handle_commitment_eq runtime repaired.application id event candidate actor payload outputEq
      codeEq node rightReady rightTimely sender owned rightVacant rightUnused,
        repaired.application.candidates.freeze_eq_self_of_not_fresh candidate rightFixed,
          sameResult]
    change some { (repaired.application.complete event rightReady action value) with
      accepted := Function.update repaired.application.accepted (.inr event) (some candidate) } = _
    rw [← accepted]

end Vegas.EventGraphRuntime.BindingMemory.Frame
