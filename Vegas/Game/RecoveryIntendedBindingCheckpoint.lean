/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryReadyCommitWitness
import Vegas.Game.CommitRecoveryIntendedInformation
import Vegas.Compile.CommitPrefixIntendedCompletion
import Vegas.Source.CommitPrefixIntendedLift

/-! # Initialized intended information at admissible concurrent binding inputs -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem prefix_observe_congr {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (first second : SourceProgram.Config Player L Δ) (who : Player)
    (same : first.view who = second.view who) :
    ProtocolState.observe who (block.prepend suffix)
        (block.liftPoint suffix (ProtocolState.entry suffix first)) =
      ProtocolState.observe who (block.prepend suffix)
        (block.liftPoint suffix (ProtocolState.entry suffix second)) := by
  induction block with
  | nil =>
      cases suffix with
      | ret => exact same
      | sample => exact congrArg Sum.inl same
      | commit => exact congrArg Sum.inl same
      | reveal => exact congrArg Sum.inl same
  | commit _ _ _ _ _ ih => exact congrArg Sum.inr (ih suffix first second same)

/-- A semantically intended saved entry and admitted actual own bindings give
a genuine initialized intended information history at a ready binding. Hidden
foreign holes are completed at updated source views, retaining the full focal
view and own word. No intended current-view witness is assumed. -/
theorem RecoverySourceCheckpoint.intended_binding_information
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) (wellFormed : setup.WellFormed)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (clear : state.entry.excluded = ∅) (stored : state.StoredCheckpoint)
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (past : List (OwnAction Player L))
    (historyAligned :
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
        state.current.native.config.store checkpoint.source).history owner = past)
    (ownAdmitted :
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
        state.current.native.config.store checkpoint.source).IntendedFor owner P) :
    ∃ site : setup.intendedModel.InformationSite owner,
      ∃ _original : setup.intendedModel.InformationHistory owner site.1,
        decodeEventView? setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (outputEmbedding setup.program).ref owner (checkpoint.embedding.event selected)
          ((serviceGraph setup mode).playerStore owner state.current.native.config.store) past =
            site.1 := by
  have decodedFilled := checkpoint.filled_prefix_view fresh guard next earlier reconstruct
    stored selected atEnd ready acting notPublication past historyAligned
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    _savedHistory, origin⟩
  dsimp only at *
  change SourceProgram.Config Player L Γ at entry
  change ContextRefs (graphLayout setup.program) Γ at refs
  change OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
    at embedding
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change Fin (eventCount program) at selected
  change earlier.prepend (.commit name owner fresh guard next) = program at reconstruct
  subst program
  let suffix : SourceProgram Player L Δ P := .commit name owner fresh guard next
  let filled := fillCommitPrefix setup.program earlier suffix embedding
    state.current.native.config.store entry
  have localIntended := origin.intended_reflect _ savedIntended
  obtain ⟨final, ⟨attempt⟩, finalIntended, sameView⟩ :=
    fillCommitPrefix_intended_completion setup.program earlier suffix embedding
      state.current.native.config.store entry entry owner localIntended rfl ownAdmitted
  let first := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (earlier.prepend suffix) entry)) ∅ state.generation
  let target := lift (earlier.liftPoint suffix (ProtocolState.entry suffix final))
  let after := first.install (target, ∅) (Finset.Subset.refl _)
  have committing : ProtocolState.atCommit setup.program first.saved = true := by
    change ProtocolState.atCommit setup.program
      (lift (ProtocolState.entry (earlier.prepend suffix) entry)) = true
    rw [commits]
    cases earlier <;> rfl
  have beforeEnd : ProtocolState.commitEnd setup.program first.saved < instructionCount suffix := by
    change ProtocolState.commitEnd setup.program
      (lift (ProtocolState.entry (earlier.prepend suffix) entry)) < instructionCount suffix
    rw [endpoints, earlier.commitEnd_suffix suffix entry final]
    exact ProtocolState.commitEnd_lt_remaining suffix (ProtocolState.entry suffix final) rfl
  have reached := attempt.reaches_unclosed_lift setup.program
    (setup.initialConfig setup.initialLaw.support_nonempty.choose) suffix lift ranks actors
      (fun point who => menus who point) steps first rfl rfl committing beforeEnd
  change (SourceProgram.commitRecoveryProtocol setup.program _).Reaches first after at reached
  have initializedClear : Nonempty (setup.commitRecoveryProtocol.Trace (some first)) := by
    rw [clear] at initialized
    exact initialized
  obtain ⟨sourceTrace⟩ := setup.recoveryTrace_of_reaches _ initializedClear reached
  have wholeIntended : ProtocolState.Intended setup.program after.point :=
    attempt.intended_lift setup.program suffix lift origin savedIntended finalIntended
  have actor : ProtocolState.actor setup.program after.point = some owner := by
    change ProtocolState.actor setup.program
      (lift (earlier.liftPoint suffix (ProtocolState.entry suffix final))) = some owner
    rw [actors, (earlier.liftPoint_recovery suffix).2.1]
    rfl
  obtain ⟨site, original, _, siteView, _⟩ := setup.commitRecovery_intendedInformation wellFormed
    after sourceTrace rfl wholeIntended owner actor
  have observed := prefix_observe_congr earlier suffix final filled owner sameView
  have wholeObserved : ProtocolState.observe owner setup.program after.point =
      ProtocolState.observe owner setup.program
        (lift (earlier.liftPoint suffix (ProtocolState.entry suffix filled))) := by
    change ProtocolState.observe owner setup.program
        (lift (earlier.liftPoint suffix (ProtocolState.entry suffix final))) = _
    rw [views.observe, views.observe, observed]
  refine ⟨site, original, ?_⟩
  exact decodedFilled.trans ((congrArg some wholeObserved).symm.trans siteView.symm)

/-- Readiness and actual checkpoint recall derive the complete own-history
alignment used by the intended counterpart. Only semantic admissibility and
the saved intended entry remain as on-path invariant obligations. -/
theorem RecoverySourceCheckpoint.intended_binding_information_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) (wellFormed : setup.WellFormed)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (clear : state.entry.excluded = ∅) (stored : state.StoredCheckpoint)
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : state.current.native.BindingInvariant) {inputs}
    (reachable : state.current.native.config.Reachable inputs)
    (retained : state.HistoryCheckpoint)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase)
    (ownAdmitted :
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
        state.current.native.config.store checkpoint.source).IntendedFor owner P) :
    ∃ site : setup.intendedModel.InformationSite owner,
      ∃ _original : setup.intendedModel.InformationHistory owner site.1,
        decodeEventView? setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (outputEmbedding setup.program).ref owner (checkpoint.embedding.event selected)
          ((serviceGraph setup mode).playerStore owner state.current.native.config.store)
          (decodeHistory setup.program (state.current.native.config.history.map
            (setup.eventGraph.fromModeCompletion mode)) owner) = site.1 := by
  exact checkpoint.intended_binding_information wellFormed fresh guard next earlier reconstruct
    clear stored savedIntended selected atEnd ready acting notPublication _
      (checkpoint.filled_prefix_history_of_ready fresh guard next earlier reconstruct clear selected
        atEnd ready acting valid reachable retained saved) ownAdmitted

end Vegas
