/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.ExcludedCommitPrefixObservation
import Vegas.Game.RecoveryReadyCommitWitness
import Vegas.Game.RecoveryReadyCommitInformation
import Vegas.Game.RevealService

/-! # Surviving source decisions with saved permanent exclusions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An actual auxiliary source actor is a played decision whenever that owner
is not excluded. Other permanent exclusions do not need to be erased. -/
theorem commitRecovery_isDecisionInfo_of_surviving_actor
    (setup : Setup (Player := Player) (L := L)) (source : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some source)) (who : Player)
    (survives : who ∉ source.excluded)
    (actor : ProtocolState.actor setup.program source.point = some who) :
    setup.commitRecoveryModel.IsDecisionInfo who (setup.commitRecoveryModel.infoOf who trace) := by
  have active : source.Active who := ⟨actor, survives⟩
  have nonterminal : ¬ setup.commitRecoveryProtocol.terminal (some source) := by
    intro terminal
    have impossible := ProtocolState.terminal_actor_none who setup.program source.point terminal
    rw [ProtocolState.actor_observe_eq, actor] at impossible
    cases impossible
  obtain ⟨joint, legal⟩ := source.progress
  have localLegal := legal who
  cases chosen : joint who with
  | none =>
      rw [chosen] at localLegal
      exact (localLegal active).elim
  | some move =>
      rw [chosen] at localLegal
      refine ⟨⟨⟨some source, trace⟩, rfl⟩, nonterminal, move, ?_⟩
      exact (setup.commitRecoveryModel.menu_adequate who trace (some move)).mpr localLegal

/-- The semantic saved source position is the actual compiled phase address. -/
theorem RecoverySourceCheckpoint.saved_position
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) :
    instructionCount setup.program - ProtocolState.remaining setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) =
      state.attempt.phase := by
  rw [checkpoint.remaining, ProtocolState.remaining_entry]
  have count := checkpoint.compiled.countEq
  simp only [eventCount_eq_instructionCount] at count
  omega

/-- A surviving owner at a ready commitment has a genuine initialized source
decision with the saved exclusion set and generation. Hidden earlier slots
are completed without inventing new misses. Its complete current source view
uses the saved source own-word followed by the actual newly read bindings;
no clear-state or given source-view premise is used. -/
theorem RecoverySourceCheckpoint.surviving_prefix_trace
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (stored : state.StoredCheckpoint) (survives : owner ∉ state.entry.excluded)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier (.commit name owner fresh guard next)
      embedding state.current.native.config.store checkpoint.source
    ∃ (source : CommitRecoveryState setup.program)
      (trace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = state.entry.excluded ∧ source.generation = state.generation ∧
      setup.commitRecoveryPublic (some source) =
        (state.entry.excluded, state.generation, state.attempt.phase) ∧
      ProtocolState.actor setup.program source.point = some owner ∧
      setup.commitRecoveryModel.IsDecisionInfo owner
        (setup.commitRecoveryModel.infoOf owner trace) ∧
      filled.history owner = ProtocolState.history setup.program source.point owner ∧
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref owner (checkpoint.embedding.event selected)
        ((serviceGraph setup mode).playerStore owner state.current.native.config.store)
        (filled.history owner) = some (ProtocolState.observe owner setup.program source.point) := by
  have savedPosition := checkpoint.saved_position
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    _savedHistory, _origin⟩
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
  have currentAgreement : refs.Agrees entry.state state.current.native.config.store := by
    intro selectedName selectedCell chosen
    apply (refs.get chosen).get?_preserved state.entry.native.config.store
      state.current.native.config.store stored
    exact agrees chosen
  have decoded := decodeObservation?_eq_some refs owner entry.state
    state.current.native.config.store currentAgreement
  have available := commitPrefix_owned_fields_of_ready setup mode earlier suffix embedding
    state.current.native.config owner selected atEnd ready acting notPublication
  obtain ⟨finished, ⟨attempt⟩, observation, word⟩ := exists_commitPrefix_attempt_observation
    setup.program earlier suffix embedding refs state.current.native.config.store entry
      state.entry.excluded owner survives decoded available
  have visibleDecode : decodeObservation? owner
      (commitBlockRefs setup.program earlier suffix embedding refs)
      ((toEventGraph setup.program).playerStore owner state.current.native.config.store) =
        some (sourceObserve owner finished.state) :=
    (decodeObservation?_playerStore (graph := toEventGraph setup.program) owner
      (commitBlockRefs setup.program earlier suffix embedding refs)
        state.current.native.config.store).trans observation
  have localView := decodeEventView?_commitPrefix_entry setup.program earlier suffix embedding
    refs ((toEventGraph setup.program).playerStore owner state.current.native.config.store) finished
      owner selected atEnd visibleDecode
  have wholeView := (views.decode owner selected
    ((toEventGraph setup.program).playerStore owner state.current.native.config.store)
      (finished.history owner)).trans
    ((congrArg (Option.map (views.view owner)) localView).trans
      (congrArg some (views.observe owner
        (earlier.liftPoint suffix (ProtocolState.entry suffix finished)))).symm)
  rw [word] at wholeView
  let first := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (earlier.prepend suffix) entry)) state.entry.excluded
      state.generation
  let target := lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished))
  let after := first.install (target, state.entry.excluded) (Finset.Subset.refl _)
  have committing : ProtocolState.atCommit setup.program first.saved = true := by
    change ProtocolState.atCommit setup.program
      (lift (ProtocolState.entry (earlier.prepend suffix) entry)) = true
    rw [commits]
    cases earlier <;> rfl
  have beforeEnd : ProtocolState.commitEnd setup.program first.saved < instructionCount suffix := by
    change ProtocolState.commitEnd setup.program
      (lift (ProtocolState.entry (earlier.prepend suffix) entry)) < instructionCount suffix
    rw [endpoints, earlier.commitEnd_suffix suffix entry finished]
    exact ProtocolState.commitEnd_lt_remaining suffix (ProtocolState.entry suffix finished) rfl
  have reached := attempt.reaches_unclosed_lift setup.program
    (setup.initialConfig setup.initialLaw.support_nonempty.choose) suffix lift ranks actors
      (fun point who => menus who point) steps first rfl rfl committing beforeEnd
  change (SourceProgram.commitRecoveryProtocol setup.program _).Reaches first after at reached
  obtain ⟨sourceTrace, _fuel, _prefix⟩ :=
    setup.recoveryTrace_of_reaches _ (Classical.choice initialized) reached
  have actor : ProtocolState.actor setup.program after.point = some owner := by
    change ProtocolState.actor setup.program
      (lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished))) = some owner
    rw [actors, (earlier.liftPoint_recovery suffix).2.1]
    rfl
  have publicSignal : setup.commitRecoveryPublic (some after) =
      (state.entry.excluded, state.generation, state.attempt.phase) := by
    change (state.entry.excluded, state.generation, instructionCount setup.program -
      ProtocolState.remaining setup.program
        (lift (ProtocolState.entry (earlier.prepend suffix) entry))) = _
    rw [savedPosition]
  refine ⟨after, sourceTrace, rfl, rfl, publicSignal, actor,
    commitRecovery_isDecisionInfo_of_surviving_actor setup after sourceTrace owner survives actor,
    ?_, wholeView⟩
  change (fillCommitPrefix setup.program earlier suffix embedding state.current.native.config.store
    entry).history owner = _
  rw [← word]
  symm
  change ProtocolState.history setup.program
    (lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished))) owner = finished.history
      owner
  rw [histories, earlier.liftPoint_history]
  rfl

/-- The actual commitment descriptor supplies the typed prefix needed for a
surviving source decision. The decoded own word is the whole source word;
physical in-phase exclusions remain separate from saved source exclusions. -/
theorem RecoverySourceCheckpoint.surviving_ready_binding_trace
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (frontier : state.Frontier) (stored : state.StoredCheckpoint)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (ready : state.current.native.config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (survives : who ∉ state.entry.excluded) :
    ∃ (source : CommitRecoveryState setup.program)
      (trace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = state.entry.excluded ∧ source.generation = state.generation ∧
      setup.commitRecoveryPublic (some source) =
        (state.entry.excluded, state.generation, state.attempt.phase) ∧
      ProtocolState.actor setup.program source.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who (setup.commitRecoveryModel.infoOf who trace) ∧
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who event
        ((serviceGraph setup mode).playerStore who state.current.native.config.store)
        (ProtocolState.history setup.program source.point who) =
          some (ProtocolState.observe who setup.program source.point) := by
  obtain ⟨selected, selectedEq, Δ, P, name, fresh, guard, next, earlier, atEnd, reconstruct⟩ :=
    checkpoint.ready_binding_prefix frontier phase remaining installed kind event inside ready
      who payload binding
  have acting : (serviceGraph setup mode).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding _ binding
  have notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication := by
    rw [binding]
    exact id
  obtain ⟨source, trace, excluded, generation, publicSignal, sourceActor, played, word, decoded⟩ :=
    checkpoint.surviving_prefix_trace fresh guard next earlier reconstruct stored survives selected
      atEnd (selectedEq.symm ▸ ready) (selectedEq.symm ▸ acting)
      (selectedEq.symm ▸ notPublication)
  rw [word, selectedEq] at decoded
  exact ⟨source, trace, excluded, generation, publicSignal, sourceActor, played, decoded⟩

end Vegas
