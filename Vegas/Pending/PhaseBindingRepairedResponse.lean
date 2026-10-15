/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingForeignResponse

/-! # Actual owner responses recording and repairing private bindings -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- The owner-local native implementation computes the actual private repair.
The saved checkpoint records the preparation but does not fabricate an early
completion. Raw/count legality of the replacement is derived from the source response. -/
theorem binding_response (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (left : PhaseCount.CountRecall runtime leaks original)
    (right : PhaseCount.CountRecall runtime leaks repaired)
    (stored : repaired.application.StoredCheckpoint)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh)
    (ready : original.application.current.native.config.cut.Ready event)
    (bounded : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (original.recall owner) (original.observe (phaseApplication runtime leaks) owner)) :
    let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
    let source : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
      | none => some (⟨payload, L.someValue payload⟩ : Raw L)
      | some _ => opening
    let target : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial),
        replacementOpening⟩, .none⟩⟩
    let view := (execution runtime leaks repaired).observe nativeApp owner
    let change := memory.repairResponse runtime (nativeLeaks (graph := graph)) owner view
      (action runtime leaks source)
    let remembered : BindingMemory runtime (nativeLeaks (graph := graph)) :=
      ⟨change.2, memory.responses ++
        [(memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view,
          action runtime leaks source)]⟩
    target ∈ PhaseCount.onePacketActions runtime leaks bounds owner (repaired.recall owner)
        (repaired.observe (phaseApplication runtime leaks) owner) ∧
      Frame runtime leaks remembered owner
        (original.respond (phaseApplication runtime leaks) owner source)
        (repaired.respond (phaseApplication runtime leaks) owner target) := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let sourceCall : Submission graph := ⟨.commitment event (owner, .prepared serial), opening⟩
  let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
    | none => some (⟨payload, L.someValue payload⟩ : Raw L)
    | some _ => opening
  let targetCall : Submission graph :=
    ⟨.commitment event (owner, .prepared serial), replacementOpening⟩
  let source : app.Action := ⟨some ⟨sourceCall, .none⟩⟩
  let target : app.Action := ⟨some ⟨targetCall, .none⟩⟩
  let view := (execution runtime leaks repaired).observe nativeApp owner
  let change := memory.repairResponse runtime (nativeLeaks (graph := graph)) owner view
    (action runtime leaks source)
  let remembered : BindingMemory runtime (nativeLeaks (graph := graph)) :=
    ⟨change.2, memory.responses ++
      [(memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view,
        action runtime leaks source)]⟩
  have openingBounded : bounds.AllowsOpening opening := by
    have allowed := member
    rw [PhaseCount.mem_onePacketActions] at allowed
    have rawMember := allowed.1
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at rawMember
    exact ((bounds.submissions_mem _ _).mp rawMember).1.2
  have replacementBounded : bounds.AllowsOpening replacementOpening := by
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none => simpa only [replacementOpening, decoded, MessageBounds.AllowsOpening] using bounded
    | some value => simpa only [replacementOpening, decoded] using openingBounded
  have legal : target ∈ PhaseCount.onePacketActions runtime leaks bounds owner
      (repaired.recall owner) (repaired.observe app owner) :=
    frame.binding_menu bounds left right event serial opening
      replacementOpening replacementBounded member
  refine ⟨legal, ?_⟩
  have actualFresh : repaired.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh := (frame.live.slots (.prepared serial)).mp fresh
  have ownFresh : (memory.shadow.inputView runtime (nativeLeaks (graph := graph))
      view).application.candidates (.prepared serial) = .fresh := by
    rw [frame.live.observed]
    exact fresh
  have localFresh : view.application.candidates (.prepared serial) = .fresh := actualFresh
  have sourceCandidates : (memory.shadow.inputView runtime (nativeLeaks (graph := graph))
      view).application.candidates =
      (original.application.current.native.playerView owner).candidates := by
    have observed : memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view =
        (execution runtime leaks original).observe nativeApp owner := frame.live.observed
    have catalogs := congrArg (fun current : nativeApp.PlayerView =>
      current.application.candidates) observed
    exact catalogs
  have changed : change.1 = action runtime leaks target := by
    dsimp only [change, source, sourceCall, action]
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        rw [memory.repairResponse_unusable runtime (nativeLeaks (graph := graph)) owner view event
          payload outputEq codeEq node serial opening ownFresh actualFresh decoded]
        simp only [target, targetCall, replacementOpening, decoded]
        rfl
    | some value =>
        rw [memory.repairResponse_usable runtime (nativeLeaks (graph := graph)) owner view event
          payload outputEq codeEq node serial opening ownFresh actualFresh value decoded]
        simp only [target, targetCall, replacementOpening, decoded]
  have native := frame.live.binding_submission event payload outputEq codeEq node serial opening
    fresh ready
  change BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
    ((execution runtime leaks original).respond nativeApp owner (action runtime leaks source))
    ((execution runtime leaks repaired).respond nativeApp owner change.1) at native
  rw [changed] at native
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
      (execution runtime leaks (original.respond app owner source))
      (execution runtime leaks (repaired.respond app owner target)) := by
    rw [execution_respond_of_onePacket runtime leaks bounds original owner source member,
      execution_respond_of_onePacket runtime leaks bounds repaired owner target legal]
    exact native
  have publicNative : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  have imageReady : repaired.application.current.native.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← publicNative, State.publicView_eventReady]
    exact ready
  have absent := saved_uncompleted_of_ready repaired.application stored event imageReady
  let catalog := memory.shadow.rememberCandidate (.prepared serial)
    (sourceCall.candidateAfter owner
      (original.application.current.native.playerView owner).candidates (.prepared serial))
  let result := (opening.bind (fun raw => raw.as? payload)).elim
    PublicationResult.failure PublicationResult.success
  have shadow : remembered.shadow = catalog.rememberCompletion event
      (cast (congrArg EventField.Action outputEq.symm)
        (result : PublicationResult (L.Val payload)))
      (cast (congrArg EventField.Value outputEq.symm)
        (result : PublicationResult (L.Val payload))) := by
    dsimp only [remembered, change, source, sourceCall, action]
    simp only [BindingMemory.repairResponse, node, ownFresh, localFresh,
      and_self, ↓reduceIte]
    rw [sourceCandidates]
  have savedOwn : remembered.shadow.view
      ((checkpoint runtime leaks (repaired.respond app owner target)).application.playerView
        owner) =
      (checkpoint runtime leaks (original.respond app owner source)).application.playerView
        owner := by
    rw [checkpoint_response_application, checkpoint_response_application, shadow]
    exact checkpoint_binding_shadow frame event serial opening
      replacementOpening absent _ _
  have savedPair := runtime.rawBinding_submit_hidden_congr (nativeLeaks (graph := graph))
    (checkpoint runtime leaks original) (checkpoint runtime leaks repaired) owner
    frame.saved.network frame.saved.receipts frame.saved.publicView frame.saved.views
    frame.saved.recall event serial opening replacementOpening
  have saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
      (checkpoint runtime leaks (original.respond app owner source))
      (checkpoint runtime leaks (repaired.respond app owner target)) := by
    apply checkpointFrame live
      (checkpoint runtime leaks (original.respond app owner source)).application
      (checkpoint runtime leaks (repaired.respond app owner target)).application
    · exact savedOwn
    · rw [checkpoint_response_application, checkpoint_response_application]
      exact savedPair.2.2.2.1
    · exact live.slots
    · rw [checkpoint_response_application, checkpoint_response_application]
      change (submitStep (sourceCall.register (checkpoint runtime leaks original).application owner)
        owner sourceCall.packet).config.store.BindingRefines
          (submitStep (targetCall.register (checkpoint runtime leaks repaired).application owner)
            owner targetCall.packet).config.store
      rw [submitStep_config, submitStep_config,
        (sourceCall.register_facts owner (checkpoint runtime leaks original).application).1,
        (targetCall.register_facts owner (checkpoint runtime leaks repaired).application).1]
      exact frame.saved.successful
  have packetEq : app.packet (app.submit original.application owner ⟨sourceCall, .none⟩) owner
      (original.network.known owner) ⟨sourceCall, .none⟩ =
      app.packet (app.submit repaired.application owner ⟨targetCall, .none⟩) owner
        (repaired.network.known owner) ⟨targetCall, .none⟩ := by
    change (original.application.submit owner ⟨sourceCall, .none⟩).emit owner
      (original.network.known owner) ⟨sourceCall, .none⟩ =
        (repaired.application.submit owner ⟨targetCall, .none⟩).emit owner
          (repaired.network.known owner) ⟨targetCall, .none⟩
    rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit]
    have attempts : original.application.attempt = repaired.application.attempt :=
      congrArg PhasePublicView.attempt frame.publicView
    change (⟨original.application.attempt, PhaseCount.maskPacket original.application.publicView
      ⟨.commitment event (owner, .prepared serial), none,
        original.application.current.native.publicView.tokenFor
          (.commitment event (owner, .prepared serial))⟩⟩ : CommitAttemptPacket graph) = _
    rw [attempts, frame.publicView, publicNative]
    rfl
  refine ⟨live, saved, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
    frame.archiveOriginal, frame.archiveRepaired, ?_, frame.service, ?_⟩
  · change (original.network.submit owner _).2 = (repaired.network.submit owner _).2
    exact congrArg₂ (fun pool packet => (pool.submit owner packet).2) frame.network packetEq
  · intro who different
    rw [app.respond_recall_other original owner who different,
      app.respond_recall_other repaired owner who different]
    exact frame.foreignRecall who different

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
