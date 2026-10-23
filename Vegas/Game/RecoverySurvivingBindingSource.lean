/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.ExcludedCommitPrefixObservation
import Vegas.Game.RecoveryCommitPrefixWitness
import Vegas.Source.ProposalRecoveryCommitWindow
import Vegas.Source.CommitPrefixSplitting
import Vegas.Source.CommitRecoveryBlockLift
import Vegas.Source.CommitRecoveryNoMissInformation
import Vegas.Source.CommitRecoveryPrefixPath

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
        (filled.history owner) = some (ProtocolState.observe owner setup.program source.point) ∧
      setup.recoveryAddressWord trace = setup.recoveryAddressWord checkpoint.trace ++
        (List.range earlier.length).map (fun index =>
          (some (state.attempt.phase + index + 1), state.entry.excluded,
            state.generation, state.attempt.phase)) ∧
      (∀ (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) observer,
        setup.proposalRecoveryArchive observer (setup.proposalRecoveryModel.infoOf observer
            (setup.proposalRecoveryLiftTrace labels trace)) =
          setup.proposalRecoveryArchive observer (setup.proposalRecoveryModel.infoOf observer
            (setup.proposalRecoveryLiftTrace labels checkpoint.trace))) := by
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
  obtain ⟨addresses, instructions, exclusions, metadata⟩ :=
    attempt.instructions_unclosed_lift setup.program
    (setup.initialConfig setup.initialLaw.support_nonempty.choose) suffix lift ranks actors
      (fun point who => menus who point) steps first rfl rfl committing beforeEnd
  change CommitRecoveryState.InstructionPath setup.program _ attempt.joints _ first after
    at instructions
  obtain ⟨sourceTrace, sourcePrefix, sourceLength, _joints, numeric⟩ :=
    setup.recoveryInstructionPath_information _ instructions initialized
  have addressLength : addresses.length = earlier.length :=
    instructions.addresses_length.trans attempt.joints_length
  have excludedWord : addresses.map (fun address => address.2.1) =
      List.replicate earlier.length state.entry.excluded :=
    exclusions.trans (attempt.exclusionsAfter_of_unchanged rfl)
  have targetRank : instructionCount setup.program -
      ProtocolState.remaining setup.program target = state.attempt.phase + earlier.length := by
    have firstRank := savedPosition
    have firstBound := ProtocolState.remaining_le_instructionCount setup.program
      (lift (ProtocolState.entry (earlier.prepend suffix) entry))
    rw [ranks, ProtocolState.remaining_entry, earlier.instructionCount_prepend] at firstRank
    rw [ranks, ProtocolState.remaining_entry, earlier.instructionCount_prepend] at firstBound
    rw [show target = lift (earlier.liftPoint suffix
      (ProtocolState.entry suffix finished)) from rfl, ranks,
      earlier.liftPoint_remaining, ProtocolState.remaining_entry]
    omega
  have ending : after.publicAddress =
      (some (state.attempt.phase + earlier.length), state.entry.excluded,
        state.generation, state.attempt.phase) := by
    change (some (instructionCount setup.program -
        ProtocolState.remaining setup.program target), state.entry.excluded,
      state.generation, instructionCount setup.program - ProtocolState.remaining setup.program
        (lift (ProtocolState.entry (earlier.prepend suffix) entry))) = _
    rw [targetRank, savedPosition]
  have exactAddresses : addresses = (List.range earlier.length).map (fun index =>
      (some (state.attempt.phase + index + 1), state.entry.excluded,
        state.generation, state.attempt.phase)) := by
    apply List.ext_getElem (by simp only [List.length_map, List.length_range, addressLength])
    intro index bound _
    have excludedAt := List.getElem_of_eq excludedWord (i := index)
      (by simpa only [List.length_map] using bound)
    have sameExcluded : (addresses[index]'bound).2.1 = state.entry.excluded := by
      simpa only [List.getElem_map, List.getElem_replicate] using excludedAt
    simp only [List.getElem_map, List.getElem_range]
    by_cases internal : index + 1 < addresses.length
    · obtain ⟨rank, generation, saved⟩ := metadata index internal
      have currentRank : (addresses[index]'bound).1 =
          some (state.attempt.phase + index + 1) := by
        dsimp only [first, CommitRecoveryState.atPoint] at rank
        rwa [savedPosition] at rank
      have savedRank : (addresses[index]'bound).2.2.2 = state.attempt.phase := by
        dsimp only [first, CommitRecoveryState.atPoint] at saved
        rwa [savedPosition] at saved
      exact Prod.ext currentRank (Prod.ext sameExcluded (Prod.ext generation savedRank))
    · have indexLast : index = addresses.length - 1 := by omega
      have positive : attempt.joints ≠ [] := by
        intro empty
        have zero := congrArg List.length empty
        rw [attempt.joints_length] at zero
        simp only [List.length_nil] at zero
        omega
      have last := instructions.last_address positive
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at last
      have addressLast : addresses[index]'bound = after.publicAddress := by
        simpa only [indexLast] using Option.some.inj last
      rw [addressLast, ending]
      have count : earlier.length = index + 1 := by omega
      rw [count, Nat.add_assoc]
  have exactNumeric : setup.recoveryAddressWord sourceTrace =
      setup.recoveryAddressWord initialized ++
        (List.range earlier.length).map (fun index =>
          (some (state.attempt.phase + index + 1), state.entry.excluded,
            state.generation, state.attempt.phase)) := by
    rw [numeric, exactAddresses]
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
    ?_, wholeView, exactNumeric, ?_⟩
  · change (fillCommitPrefix setup.program earlier suffix embedding
      state.current.native.config.store entry).history owner = _
    rw [← word]
    symm
    change ProtocolState.history setup.program
      (lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished))) owner =
        finished.history owner
    rw [histories, earlier.liftPoint_history]
    rfl
  · intro labels observer
    apply setup.proposalRecoveryArchive_eq_of_commit_window observer first
      (setup.proposalRecoveryLiftTrace labels initialized) committing
      (setup.proposalRecoveryLiftTrace labels sourceTrace)
      (setup.proposalRecoveryLiftTrace_prefix labels sourcePrefix.tracePrefix)
    simp only [setup.proposalRecoveryLiftTrace_length]
    have count := attempt.joints_length
    have savedEnd : ProtocolState.commitEnd setup.program first.point < instructionCount suffix :=
      beforeEnd
    have remaining : ProtocolState.remaining setup.program first.point =
        earlier.length + instructionCount suffix := by
      dsimp only [first, CommitRecoveryState.atPoint]
      rw [ranks, ProtocolState.remaining_entry, earlier.instructionCount_prepend]
    omega

end Vegas
