/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceBindingOrigin
import Vegas.Game.PhaseBindingSourceAdmission
import Vegas.Game.PhaseCommitReadStability
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Pending.CompletedBindingReadback

/-! # Original admitted bindings extend the same surviving source prefix -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A stamped raw binding extends the same checkpoint at its authentic callback.
Immutable native reads are transported through the real trace and raw completion. -/
theorem phase_stamped_binding_admitted
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (binding : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload)
    (nativeImage : EventGraphRuntime.State (serviceGraph setup mode))
    (validImage : nativeImage.BindingInvariant)
    (results : ∀ handle payload, nativeImage.bindingResult handle payload =
      control.execution.application.current.native.bindingResult handle payload)
    (stamped : BindingStamp (fun who => (phaseApplication runtime leaks).outputs
      (control.execution.recall who)) control.execution.application.attempt nativeImage)
    (preservedImage : KeepsStore control.execution.application.current.native nativeImage)
    (candidate : Handle (serviceGraph setup mode))
    (accepted : nativeImage.accepted
      (.inr (checkpoint.embedding.event selected)) = some candidate)
    (lower : control.execution.application.attempt.phase ≤
      (checkpoint.embedding.event selected).val)
    (consistent : (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      owner).Consistent (control.execution.recall owner))
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (priorAdmitted : ∀ (before : (phaseApplication runtime leaks).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before)),
      TracePrefix prior trace →
      before.execution.application.attempt = control.execution.application.attempt →
      before.execution.application.current.native.config.cut.Ready
        (checkpoint.embedding.event selected) →
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
        before.execution.application.current.native.config.store checkpoint.source).IntendedFor
          owner P) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier (.commit name owner fresh guard next)
      embedding nativeImage.config.store checkpoint.source
    ∃ value,
      nativeImage.bindingResult candidate payload =
        .success value ∧
      (⟨.inr (checkpoint.embedding.event selected), binding⟩ :
        FieldRef (serviceGraph setup mode).layout (.binding owner payload)).get?
          nativeImage.config.store = some (.success value) ∧
      guard.predicts (sourceObserve owner filled.state) value = true ∧
      (commitSuccessor name guard filled (.success value)).IntendedFor owner (insert name P) := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  obtain ⟨before, prior, entry, serial, choice, retainedTrace, sameAttempt, acting, beforeClear,
    request, _retained, _viewed, _fresh, supported, _nonmissing, _declared, _candidate,
    immutable⟩ := phase_binding_source_choice_of_stamp setup mode runtime leaks bounds wellFormed
      assessment plan maximal inputs horizon scheduler trace clear owner
        (checkpoint.embedding.event selected) payload binding nativeImage validImage results stamped
          candidate accepted lower consistent
  have rawBefore := menu.toRawTrace initial horizon scheduler prior
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized rawBefore
  have sameEntry := phase_entry_of_same_attempt_prefix runtime leaks menu initial initialized
    horizon scheduler before control prior trace retainedTrace ordered sameAttempt
  have generation : before.execution.application.generation =
      control.execution.application.generation := congrArg CommitAttemptId.generation sameAttempt
  have position : before.execution.application.attempt.phase =
      control.execution.application.attempt.phase := congrArg CommitAttemptId.phase sameAttempt
  let author := checkpoint.transfer sameEntry generation position
  have failureRecord := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    rawBefore
  have authorClear : before.execution.application.entry.excluded = ∅ :=
    Finset.subset_empty.mp (beforeClear ▸ failureRecord.inherited)
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler rawBefore
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawBefore
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    rawBefore
  have histories := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    rawBefore
  have frontier := (phaseApplication_frontier runtime leaks).history initial horizon scheduler (by
    intro state positive
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
    exact PhaseRuntimeState.initial_frontier plan draw) rawBefore
  have saved : before.execution.application.entry.native.config.cut.IsPrefix
      before.execution.application.attempt.phase := by
    obtain ⟨current, head, _member⟩ := request.2.1
    cases phases : before.execution.application.phases with
    | nil => simp only [phases, List.head?_nil, Option.mem_def, reduceCtorEq] at head
    | cons active remaining =>
        have positioned := frontier.positioned
        rw [phases] at positioned
        simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
          Option.getD_some] using positioned.1
  have beforeAdmitted := priorAdmitted before prior retainedTrace sameAttempt request.2.2.1
  obtain ⟨value, typed, predictsBefore, _nextBefore⟩ := phase_binding_source_choice_admitted
    setup mode runtime leaks wellFormed source assessment.strategy copies before.execution author
      fresh guard next earlier reconstruct authorClear stored savedIntended selected atEnd
        request.2.2.1 request.2.2.2.1 binding bindings.active native.active.reachable histories
          saved beforeAdmitted choice supported
  have result : nativeImage.bindingResult candidate payload =
      .success value := immutable.trans (congrArg Prod.fst typed)
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, sourceEntry, refs, registry, embedding, beforeCut,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, sourceHistories, memories, steps, menus, readout, initializedSource,
    views, savedHistory, origin⟩
  dsimp only at *
  change SourceProgram.Config Player L Γ at sourceEntry
  change OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
    at embedding
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change Fin (eventCount program) at selected
  change earlier.prepend (.commit name owner fresh guard next) = program at reconstruct
  subst program
  let suffix : SourceProgram Player L Δ P := .commit name owner fresh guard next
  have notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event selected)).IsPublication := by
    rw [binding]
    simp only [EventField.IsPublication, not_false_eq_true]
  have preservedBefore := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial
    horizon scheduler before control prior trace retainedTrace clear).2.1
  have preserved : KeepsStore before.execution.application.current.native nativeImage := by
    intro field value installed
    exact preservedImage field value (preservedBefore field value installed)
  have available := commitPrefix_owned_fields_of_ready setup mode earlier suffix embedding
    before.execution.application.current.native.config owner selected atEnd request.2.2.1
      request.2.2.2.1 notPublication
  have views := fillCommitPrefix_view_of_extension setup.program earlier suffix embedding
    before.execution.application.current.native.config.store nativeImage.config.store sourceEntry
      owner preserved available
  have predicts : guard.predicts (sourceObserve owner (fillCommitPrefix setup.program earlier
      suffix embedding nativeImage.config.store sourceEntry).state) value = true := by
    have same := congrArg (fun view => guard.predicts view value) (congrArg Prod.fst views)
    exact same.symm.trans predictsBefore
  have currentAdmitted := fillCommitPrefix_intendedFor_of_extension setup.program earlier suffix
    embedding before.execution.application.current.native.config.store nativeImage.config.store
      sourceEntry owner preserved available beforeAdmitted
  have completed := validImage.toAssociationInvariant.accepted_complete
    (embedding.event selected) candidate accepted
  let ref : FieldRef (serviceGraph setup mode).layout (.binding owner payload) :=
    ⟨.inr (embedding.event selected), binding⟩
  have read := validImage.binding_read ref (embedding.event selected) rfl completed
  change ref.get? nativeImage.config.store =
    some ((nativeImage.accepted
      (.inr (embedding.event selected))).elim .failure (fun handle =>
        nativeImage.bindingResult handle payload)) at read
  rw [accepted, Option.elim_some, result] at read
  exact ⟨value, result, read, predicts, currentAdmitted.commit_own fresh guard value predicts⟩

/-- Every surviving accepted own binding extends its fixed checkpoint's actual
filled prefix. Prior admission is required only at the authentic earlier callback
of this same history; the checkpoint is transferred, never independently chosen. -/
theorem phase_completed_binding_admitted
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (binding : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload)
    (candidate : Handle (serviceGraph setup mode))
    (accepted : control.execution.application.current.native.accepted
      (.inr (checkpoint.embedding.event selected)) = some candidate)
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : control.execution.application.phases.head? = some phase)
    (inside : checkpoint.embedding.event selected ∈ phase.events)
    (consistent : (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      owner).Consistent (control.execution.recall owner))
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (priorAdmitted : ∀ (before : (phaseApplication runtime leaks).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before)),
      TracePrefix prior trace →
      before.execution.application.attempt = control.execution.application.attempt →
      before.execution.application.current.native.config.cut.Ready
        (checkpoint.embedding.event selected) →
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
        before.execution.application.current.native.config.store checkpoint.source).IntendedFor
          owner P) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier (.commit name owner fresh guard next)
      embedding control.execution.application.current.native.config.store checkpoint.source
    ∃ value,
      control.execution.application.current.native.bindingResult candidate payload =
        .success value ∧
      (⟨.inr (checkpoint.embedding.event selected), binding⟩ :
        FieldRef (serviceGraph setup mode).layout (.binding owner payload)).get?
          control.execution.application.current.native.config.store = some (.success value) ∧
      guard.predicts (sourceObserve owner filled.state) value = true ∧
      (commitSuccessor name guard filled (.success value)).IntendedFor owner (insert name P) := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
  have lower := ((phase.mem_events (checkpoint.embedding.event selected)).mp inside).1
  have address : control.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  rw [← address] at lower
  exact phase_stamped_binding_admitted setup mode runtime leaks bounds wellFormed source assessment
    copies plan maximal inputs horizon scheduler trace clear checkpoint fresh guard next earlier
      reconstruct selected atEnd binding control.execution.application.current.native
        bindings.active (fun _ _ => rfl) stamped (fun _ _ installed => installed) candidate accepted
          lower consistent savedIntended priorAdmitted

end Vegas
