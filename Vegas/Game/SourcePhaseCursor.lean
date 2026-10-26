/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseSurvivingSourceView
import Vegas.Game.CompiledCommitState
import Vegas.Game.CompiledCommitPrefixExclusions
import Vegas.Game.CompiledCommitSurvivingView
import Vegas.Game.CompiledCommitExclusionWord
import Vegas.Source.CommitRecoveryPrefixPath

/-! # Current source cursors inside sequential maximal commitment phases

The actual completed predecessor prefix is decoded from accepted native binding
meanings. Missing receipts cause actual source exclusions; accepted unusable
bindings remain latent. Legal source recovery instructions preserve the saved
checkpoint until the maximal phase closes. Retired own observations are kept.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]

namespace EventGraphRuntime.PhaseRuntimeState

variable {graph : Vegas.EventGraph Player L}

/-- The actual source address scan through the current prefix, including
permanent exclusions introduced since the saved boundary. -/
def sourceCurrentAddressWord (plan : RuntimePhasePlan graph) (state : PhaseRuntimeState graph)
    (eventRank : Nat) : List (Option Nat × (Finset Player × Nat × Nat)) :=
  state.sourcePublicAddressWord plan state.attempt.phase ++
    (List.range (eventRank - state.attempt.phase)).map fun index =>
      (some (state.attempt.phase + index + 1),
        archivedFailureOwners state.retired ∪
          state.current.native.failureOwnersBefore (state.attempt.phase + index + 1),
        state.generation, state.attempt.phase)

/-- This scan uses only the literal public runtime observation. -/
theorem sourceCurrentAddressWord_congr (plan : RuntimePhasePlan graph)
    {first second : PhaseRuntimeState graph} (same : first.publicView = second.publicView)
    (eventRank : Nat) :
    first.sourceCurrentAddressWord plan eventRank =
      second.sourceCurrentAddressWord plan eventRank := by
  have native : first.current.native.publicView = second.current.native.publicView :=
    congrArg PhasePublicView.native same
  have archives : first.retired.map (fun record => (record.attempt, record.state.publicView)) =
      second.retired.map (fun record => (record.attempt, record.state.publicView)) :=
    congrArg PhasePublicView.retired same
  have attempt : first.attempt = second.attempt := congrArg PhasePublicView.attempt same
  have generation : first.generation = second.generation := by
    exact congrArg (fun value => value.generation) attempt
  have archived := archivedFailureOwners_eq_of_publicViews_eq first.retired second.retired archives
  have saved := sourcePublicAddressWord_congr plan same first.attempt.phase
  simp only [sourceCurrentAddressWord]
  rw [saved]
  simp only [attempt, archived, generation, State.failureOwnersBefore_congr native]

end EventGraphRuntime.PhaseRuntimeState

/-- The actual completed binding prefix has its literal source install,
source joint recall and legal source trace, including all in-phase omissions.
The saved checkpoint is retained until the real source close. -/
theorem RecoverySourceCheckpoint.current_binding_prefix_trace
    {setup : Setup (Player := Player) (L := L)}
    {state : PhaseRuntimeState (serviceGraph setup .sequential)}
    (checkpoint : RecoverySourceCheckpoint setup .sequential state)
    (phase : RuntimePhase (serviceGraph setup .sequential))
    (remaining : List (RuntimePhase (serviceGraph setup .sequential)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (stored : state.StoredCheckpoint) (receipts : state.ReceiptRecord)
    (valid : state.current.native.BindingInvariant)
    (archives : state.ArchivedExclusions) (savedFailures : state.PublicFailureCheckpoint)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (survives : owner ∉ state.current.excluded) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier (.commit name owner fresh guard next)
      embedding state.current.native.config.store checkpoint.source
    let suffix : SourceProgram Player L Δ P := .commit name owner fresh guard next
    let decoded := decodeCommitAttempt setup.program .sequential earlier suffix embedding
      state.current.native checkpoint.source state.entry.excluded
    let first := CommitRecoveryState.atPoint (checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) state.entry.excluded
        state.generation
    let target := checkpoint.residual.lift (cast (congrArg ProtocolState reconstruct)
      (earlier.liftPoint suffix (ProtocolState.entry suffix decoded.1)))
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source = first.install (target, decoded.2.1) decoded.2.2.excluded_subset ∧
      TracePrefix checkpoint.trace sourceTrace ∧
      source.excluded = state.current.excluded ∧ source.generation = state.generation ∧
      setup.commitRecoveryPublic (some source) =
        (state.current.excluded, state.generation, state.attempt.phase) ∧
      ProtocolState.actor setup.program source.point = some owner ∧
      setup.commitRecoveryModel.IsDecisionInfo owner
        (setup.commitRecoveryModel.infoOf owner sourceTrace) ∧
      filled.history owner = ProtocolState.history setup.program source.point owner ∧
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref owner (checkpoint.embedding.event selected)
        ((serviceGraph setup .sequential).playerStore owner state.current.native.config.store)
        (ProtocolState.history setup.program source.point owner) =
          some (ProtocolState.observe owner setup.program source.point) ∧
      setup.recoveryAddressWord sourceTrace = setup.recoveryAddressWord checkpoint.trace ++
        (List.range earlier.length).map (fun index =>
          (some (state.attempt.phase + index + 1),
            PhaseRuntimeState.archivedFailureOwners state.retired ∪
              state.current.native.failureOwnersBefore (state.attempt.phase + index + 1),
            state.generation, state.attempt.phase)) ∧
      setup.recoveryJointRecall sourceTrace = decoded.2.2.joints.reverse ++
        setup.recoveryJointRecall checkpoint.trace := by
  classical
  have savedPosition := checkpoint.saved_position
  have low : phase.low = state.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have member : phase ∈ state.phases.head? := by
    simp only [installed, List.head?_cons, Option.mem_some_iff]
  have receiptOrder := receipts.ordered phase member kind
  rw [low] at receiptOrder
  have evidence := receipts.exclusion.installed phase member
  rw [low] at evidence
  have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    have positioned := receipts.exclusion.frontier.positioned
    rw [installed] at positioned
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using positioned.1
  have excludedBefore : state.entry.excluded =
      PhaseRuntimeState.archivedFailureOwners state.retired ∪
        state.current.native.failureOwnersBefore state.attempt.phase := by
    rw [archives.saved_eq, ← savedFailures.failureOwnersBefore_eq state.attempt.phase saved]
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
  let decoded := decodeCommitAttempt setup.program .sequential earlier suffix embedding
    state.current.native entry state.entry.excluded
  have processed (index : Fin (eventCount (earlier.prepend suffix)))
      (inside : index.val < earlier.length) :
      embedding.event index ∈ state.current.native.config.cut.completed := by
    apply ((toEventGraph setup.program).sequentialize_mem_completed_iff_lt_of_ready
      state.current.native.config.cut ready).mpr
    rw [compiled.rankEq, compiled.rankEq, atEnd]
    omega
  have excluded : decoded.2.1 = state.current.excluded := by
    rw [decodeCommitAttempt_excluded_eq_public_prefix setup.program .sequential earlier suffix
      embedding state.attempt.phase compiled.rankEq state.current.native processed entry
      state.entry.excluded]
    ext who
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [evidence.excluded]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨event, lower, _upper, acting, failed⟩
      exact ⟨event, lower, acting, failed⟩
    · rintro ⟨event, lower, acting, failed⟩
      have upper := ((toEventGraph setup.program).sequentialize_mem_completed_iff_lt_of_ready
        state.current.native.config.cut ready).mp failed.completed
      rw [compiled.rankEq, atEnd] at upper
      exact ⟨event, lower, upper, acting, failed⟩
  have currentAgreement : refs.Agrees entry.state state.current.native.config.store := by
    intro selectedName selectedCell chosen
    exact (refs.get chosen).get?_preserved _ _ stored _ (agrees chosen)
  have fullAgreement : (commitBlockRefs setup.program earlier suffix embedding refs).Agrees
      decoded.1.state state.current.native.config.store := by
    exact decodeCommitAttempt_state_agrees setup.program .sequential earlier suffix embedding refs
      state.current.native entry state.entry.excluded state.attempt.phase compiled.rankEq valid
      receiptOrder currentAgreement processed
  have visibleDecode := (decodeObservation?_playerStore (graph := toEventGraph setup.program)
    owner (commitBlockRefs setup.program earlier suffix embedding refs)
    state.current.native.config.store).trans
      (decodeObservation?_eq_some _ owner decoded.1.state _ fullAgreement)
  have localView := decodeEventView?_commitPrefix_entry setup.program earlier suffix embedding
    refs ((toEventGraph setup.program).playerStore owner state.current.native.config.store)
    decoded.1 owner selected atEnd visibleDecode
  have wholeView := (views.decode owner selected
    ((toEventGraph setup.program).playerStore owner state.current.native.config.store)
      (decoded.1.history owner)).trans
    ((congrArg (Option.map (views.view owner)) localView).trans
      (congrArg some (views.observe owner
        (earlier.liftPoint suffix (ProtocolState.entry suffix decoded.1)))).symm)
  let first := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (earlier.prepend suffix) entry)) state.entry.excluded
      state.generation
  let target := lift (earlier.liftPoint suffix (ProtocolState.entry suffix decoded.1))
  let after := first.install (target, decoded.2.1) decoded.2.2.excluded_subset
  have committing : ProtocolState.atCommit setup.program first.saved = true := by
    change ProtocolState.atCommit setup.program
      (lift (ProtocolState.entry (earlier.prepend suffix) entry)) = true
    rw [commits]
    cases earlier <;> rfl
  have beforeEnd : ProtocolState.commitEnd setup.program first.saved < instructionCount suffix := by
    change ProtocolState.commitEnd setup.program
      (lift (ProtocolState.entry (earlier.prepend suffix) entry)) < instructionCount suffix
    rw [endpoints, earlier.commitEnd_suffix suffix entry decoded.1]
    exact ProtocolState.commitEnd_lt_remaining suffix (ProtocolState.entry suffix decoded.1) rfl
  obtain ⟨addresses, instructions, exclusions, metadata⟩ :=
    decoded.2.2.instructions_unclosed_lift setup.program
      (setup.initialConfig setup.initialLaw.support_nonempty.choose) suffix lift ranks actors
      (fun point who => menus who point) steps first rfl rfl committing beforeEnd
  change CommitRecoveryState.InstructionPath setup.program _ decoded.2.2.joints _ first after
    at instructions
  obtain ⟨sourceTrace, sourcePrefix, _sourceLength, joints, numeric⟩ :=
    setup.recoveryInstructionPath_information _ instructions initialized
  have addressLength : addresses.length = earlier.length :=
    instructions.addresses_length.trans decoded.2.2.joints_length
  have excludedWord := exclusions.trans (decodeCommitAttempt_exclusionWord_scan
    setup.program .sequential earlier suffix embedding state.current.native
    state.attempt.phase compiled.rankEq processed entry state.entry.excluded
    (PhaseRuntimeState.archivedFailureOwners state.retired) excludedBefore)
  have targetRank : instructionCount setup.program -
      ProtocolState.remaining setup.program target = state.attempt.phase + earlier.length := by
    have firstRank := savedPosition
    have firstBound := ProtocolState.remaining_le_instructionCount setup.program
      (lift (ProtocolState.entry (earlier.prepend suffix) entry))
    rw [ranks, ProtocolState.remaining_entry, earlier.instructionCount_prepend] at firstRank
    rw [ranks, ProtocolState.remaining_entry, earlier.instructionCount_prepend] at firstBound
    rw [show target = lift (earlier.liftPoint suffix
      (ProtocolState.entry suffix decoded.1)) from rfl, ranks,
      earlier.liftPoint_remaining, ProtocolState.remaining_entry]
    omega
  have ending : after.publicAddress =
      (some (state.attempt.phase + earlier.length), state.current.excluded,
        state.generation, state.attempt.phase) := by
    change (some (instructionCount setup.program -
        ProtocolState.remaining setup.program target), decoded.2.1,
      state.generation, instructionCount setup.program - ProtocolState.remaining setup.program
        (lift (ProtocolState.entry (earlier.prepend suffix) entry))) = _
    rw [targetRank, savedPosition, excluded]
  have exactAddresses : addresses = (List.range earlier.length).map (fun index =>
      (some (state.attempt.phase + index + 1),
        PhaseRuntimeState.archivedFailureOwners state.retired ∪
          state.current.native.failureOwnersBefore (state.attempt.phase + index + 1),
        state.generation, state.attempt.phase)) := by
    apply List.ext_getElem (by simp only [List.length_map, List.length_range, addressLength])
    intro index bound _
    have excludedAt := List.getElem_of_eq excludedWord (i := index)
      (by simpa only [List.length_map] using bound)
    have sameExcluded : (addresses[index]'bound).2.1 =
        PhaseRuntimeState.archivedFailureOwners state.retired ∪
          state.current.native.failureOwnersBefore (state.attempt.phase + index + 1) := by
      simpa only [List.getElem_map, List.getElem_range] using excludedAt
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
      have positive : decoded.2.2.joints ≠ [] := by
        intro empty
        have zero := congrArg List.length empty
        rw [decoded.2.2.joints_length] at zero
        simp only [List.length_nil] at zero
        omega
      have last := instructions.last_address positive
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at last
      have addressLast : addresses[index]'bound = after.publicAddress := by
        simpa only [indexLast] using Option.some.inj last
      apply Prod.ext
      · rw [addressLast, ending]
        have count : earlier.length = index + 1 := by omega
        simp only
        congr 1
        omega
      · apply Prod.ext sameExcluded
        rw [addressLast, ending]
  have actor : ProtocolState.actor setup.program after.point = some owner := by
    change ProtocolState.actor setup.program target = some owner
    rw [actors, (earlier.liftPoint_recovery suffix).2.1]
    rfl
  have publicSignal : setup.commitRecoveryPublic (some after) =
      (state.current.excluded, state.generation, state.attempt.phase) := by
    change (decoded.2.1, state.generation, instructionCount setup.program -
      ProtocolState.remaining setup.program
        (lift (ProtocolState.entry (earlier.prepend suffix) entry))) = _
    rw [excluded, savedPosition]
  have active : owner ∉ after.excluded := by
    change owner ∉ decoded.2.1
    rwa [excluded]
  have sourceWord : ProtocolState.history setup.program after.point owner =
      decoded.1.history owner := by
    change ProtocolState.history setup.program target owner = _
    rw [histories, earlier.liftPoint_history]
    rfl
  have sameView := decodeCommitAttempt_surviving_view_eq_fill setup.program .sequential earlier
    suffix embedding state.current.native valid owner entry entry state.entry.excluded rfl
      (fun index inside _owned => processed index inside) (by rwa [excluded])
  have sameWord : decoded.1.history owner =
      (fillCommitPrefix setup.program earlier suffix embedding
        state.current.native.config.store entry).history owner := congrArg Prod.snd sameView
  refine ⟨after, sourceTrace, rfl, sourcePrefix.tracePrefix, excluded, rfl, publicSignal, actor,
    commitRecovery_isDecisionInfo_of_surviving_actor setup after sourceTrace owner active actor,
    sameWord.symm.trans sourceWord.symm, ?_, ?_, joints⟩
  · rw [sourceWord]
    exact wholeView
  · rw [numeric, exactAddresses]

/-- Every actual initialized sequential binding request has a legal current
source cursor, with all in-phase omissions and retained own observations.
The source address scan is a function of public runtime information. -/
theorem phase_ready_binding_current_source
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (serviceGraph setup .sequential))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup .sequential)))
    (plan : RuntimePhasePlan (serviceGraph setup .sequential))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .sequential).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.current.excluded ∧
      source.generation = control.execution.application.generation ∧
      setup.commitRecoveryPublic (some source) =
        (control.execution.application.current.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase) ∧
      ProtocolState.actor setup.program source.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      phaseSurvivingSourceView? setup .sequential runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) =
          some (ProtocolState.observe who setup.program source.point) ∧
      setup.recoveryAddressWord sourceTrace =
        control.execution.application.sourceCurrentAddressWord plan event.val := by
  let inputs : PMF (serviceGraph setup .sequential).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨checkpoint, archivedRecall, publicChronology, _sourceOrigin⟩ :=
    recoverySourceCheckpoint_history setup .sequential runtime leaks plan maximal horizon
      scheduler trace
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have bindingRecord := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have retained := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have receipts := phaseReceiptRecord_history runtime leaks
    (serviceGraph_revealRelaxedOrdered setup .sequential) plan inputs horizon scheduler
      physicalTrace
  obtain ⟨_input, native⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler physicalTrace
  have archives := PhaseRuntimeState.archivesBefore_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have archiveExclusions := phaseArchivedExclusions_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have savedFailures := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have survives : who ∉ control.execution.application.entry.excluded :=
    fun member => request.2.2.2.2 (coverage.inherited member)
  obtain ⟨phase, remaining, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup .sequential) maximal inputs horizon scheduler
      physicalTrace who event payload binding request.2.2.1
  obtain ⟨selected, selectedEq, Δ, P, name, fresh, guard, next, earlier, atEnd, reconstruct⟩ :=
    checkpoint.ready_binding_prefix exclusion.frontier phase remaining installed kind event inside
      request.2.2.1 who payload binding
  obtain ⟨source, sourceTrace, _installedSource, _prefix, excluded, generation, publicSignal, actor,
      played, word, decoded, numeric, _joints⟩ :=
    checkpoint.current_binding_prefix_trace phase remaining
    installed kind stored receipts bindingRecord.active archiveExclusions savedFailures fresh guard
    next earlier reconstruct selected atEnd (selectedEq.symm ▸ request.2.2.1) request.2.2.2.2
  have saved : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase := by
    have positioned := exclusion.frontier.positioned
    rw [installed] at positioned
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using positioned.1
  have acting : (serviceGraph setup .sequential).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding _ binding
  have actualWord := checkpoint.filled_prefix_archived_history_of_ready archivedRecall archives
    fresh guard next earlier reconstruct survives selected atEnd (selectedEq.symm ▸ request.2.2.1)
      (selectedEq.symm ▸ acting) bindingRecord.active native.active.reachable retained saved
  rw [← word, selectedEq] at decoded
  have eventRank : event.val = control.execution.application.attempt.phase + earlier.length := by
    rw [← selectedEq, checkpoint.compiled.rankEq, atEnd]
  refine ⟨source, sourceTrace, excluded, generation, publicSignal, actor, played, ?_, ?_⟩
  · rw [phaseSurvivingSourceView?_observed_of_history setup .sequential runtime leaks plan inputs
      horizon scheduler physicalTrace who event, ← actualWord]
    exact decoded
  · rw [numeric, publicChronology.addresses]
    simp only [PhaseRuntimeState.sourceCurrentAddressWord, eventRank, Nat.add_sub_cancel_left]

end Vegas
