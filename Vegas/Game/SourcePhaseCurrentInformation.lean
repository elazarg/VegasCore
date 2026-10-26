/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseClient
import Vegas.Game.RecoveryCheckpointHistory
import Vegas.Game.CommitAttemptSurvivingRecall

/-! # Full surviving own histories at actual sequential source cursors -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem atCommit_cast {Γ : SourceCtx Player L} {O : Finset VarId}
    {first second : SourceProgram Player L Γ O} (same : first = second)
    (point : ProtocolState first) :
    ProtocolState.atCommit second (cast (congrArg ProtocolState same) point) =
      ProtocolState.atCommit first point := by
  cases same
  rfl

omit [Fintype Player] in
theorem RecoverySourceCheckpoint.current_binding_prefix_archived_history
    {setup : Setup (Player := Player) (L := L)}
    {state : PhaseRuntimeState (serviceGraph setup .sequential)}
    (checkpoint : RecoverySourceCheckpoint setup .sequential state)
    (aligned : checkpoint.ArchivedRecall) (archives : state.ArchivesBefore)
    (valid : state.current.native.BindingInvariant) {inputs}
    (reachable : state.current.native.config.Reachable inputs)
    (retained : state.HistoryCheckpoint)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected)) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let suffix : SourceProgram Player L Δ P := .commit name owner fresh guard next
    let decoded := decodeCommitAttempt setup.program .sequential earlier suffix embedding
      state.current.native checkpoint.source state.entry.excluded
    let target := checkpoint.residual.lift (cast (congrArg ProtocolState reconstruct)
      (earlier.liftPoint suffix (ProtocolState.entry suffix decoded.1)))
    ∀ observer, observer ∉ decoded.2.1 →
      ProtocolState.history setup.program target observer =
        decodeHistory setup.program
          ((PhaseRuntimeState.archivedHistory state.retired state.current.native.config.history).map
            ((toEventGraph setup.program).fromModeCompletion .sequential)) observer := by
  have rank := checkpoint.compiled.rankEq
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    _savedHistory, _origin⟩
  dsimp only at *
  change SourceProgram.Config Player L Γ at entry
  change OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
    at embedding
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change Fin (eventCount program) at selected
  change earlier.prepend (.commit name owner fresh guard next) = program at reconstruct
  subst program
  let suffix : SourceProgram Player L Δ P := .commit name owner fresh guard next
  let decoded := decodeCommitAttempt setup.program .sequential earlier suffix embedding
    state.current.native entry state.entry.excluded
  have finished : state.current.native.config.cut.IsPrefix (state.attempt.phase + earlier.length) :=
    by
      constructor
      · change state.attempt.phase + earlier.length ≤ eventCount setup.program
        have bound := (embedding.event selected).isLt
        rw [rank selected, atEnd] at bound
        change state.attempt.phase + earlier.length < eventCount setup.program at bound
        omega
      · intro event
        rw [(toEventGraph setup.program).sequentialize_mem_completed_iff_lt_of_ready
          state.current.native.config.cut ready, rank selected, atEnd]
  intro observer surviving
  have inherited : observer ∉ state.entry.excluded :=
    fun member => surviving (decoded.2.2.excluded_subset member)
  have sourceWord := decodeCommitAttempt_history_extension_of_survivor setup.program .sequential
    earlier suffix embedding state.attempt.phase rank state.entry.native state.current.native
    entry state.entry.excluded observer surviving valid reachable retained saved finished
    views.actionEq
  have oldWord := aligned observer inherited
  have physicalWord := decodeArchivedHistory_checkpoint_extension setup.program .sequential
    state.retired state.entry.native.config state.current.native.config state.attempt.phase
    archives saved retained observer
  change ProtocolState.history setup.program
    (lift (earlier.liftPoint suffix (ProtocolState.entry suffix decoded.1))) observer = _
  rw [histories, earlier.liftPoint_history]
  change decoded.1.history observer = _
  rw [sourceWord, oldWord]
  exact physicalWord.symm

/-- The same actual current source history reads full original information
for every surviving player, including those not currently active. -/
theorem phase_ready_binding_current_information
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (serviceGraph setup .sequential))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup .sequential)))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (SourcePhaseClient.initial setup runtime leaks) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .sequential).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.current.excluded ∧
      ProtocolState.actor setup.program source.point = some who ∧
      ProtocolState.atCommit setup.program source.point = true ∧
      instructionCount setup.program - ProtocolState.remaining setup.program source.point =
        event.val ∧
      ∀ observer, observer ∉ control.execution.application.current.excluded →
        SourcePhaseClient.information? setup runtime leaks observer event
            (control.execution.observe (phaseApplication runtime leaks) observer) =
          some (setup.commitRecoveryModel.infoOf observer sourceTrace) := by
  let plan := SourcePhaseClient.plan setup
  have maximal := compiledRuntimePhasePlan_maximal setup.program .sequential
  let inputs : PMF (serviceGraph setup .sequential).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨witness⟩ := recoverySourceWitness_history setup .sequential runtime leaks plan maximal
    horizon scheduler trace
  let checkpoint := witness.checkpoint
  obtain ⟨_input, native⟩ := witness.native
  obtain ⟨phase, remaining, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup .sequential) maximal inputs horizon scheduler
      physicalTrace who event payload binding request.2.2.1
  obtain ⟨selected, selectedEq, Δ, P, name, fresh, guard, next, earlier, atEnd, reconstruct⟩ :=
    checkpoint.ready_binding_prefix witness.receipts.exclusion.frontier phase remaining installed
      kind event inside
      request.2.2.1 who payload binding
  obtain ⟨source, sourceTrace, installedSource, _prefix, excluded, _generation, _publicSignal,
      actor, _played, _word, decoded, numeric, _joints⟩ :=
    checkpoint.current_binding_prefix_trace phase remaining
    installed kind witness.stored witness.receipts witness.binding.active witness.exclusions
    witness.failures fresh guard next earlier reconstruct selected atEnd
      (selectedEq.symm ▸ request.2.2.1) request.2.2.2.2
  have saved : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase := by
    have positioned := witness.receipts.exclusion.frontier.positioned
    rw [installed] at positioned
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using positioned.1
  have nativeWord := checkpoint.current_binding_prefix_archived_history witness.aligned
    witness.archives witness.binding.active native.active.reachable witness.remembered saved fresh
      guard next earlier reconstruct selected atEnd (selectedEq.symm ▸ request.2.2.1)
  have actualWord (observer : Player)
      (active : observer ∉ control.execution.application.current.excluded) :
      ProtocolState.history setup.program source.point observer =
        decodeHistory setup.program
          ((PhaseRuntimeState.archivedHistory control.execution.application.retired
            control.execution.application.current.native.config.history).map
              ((toEventGraph setup.program).fromModeCompletion .sequential)) observer := by
    have sourceActive : observer ∉ source.excluded := by rwa [excluded]
    rw [installedSource]
    exact nativeWord observer (by
      simpa only [installedSource, CommitRecoveryState.install] using sourceActive)
  have eventRank : event.val = control.execution.application.attempt.phase + earlier.length := by
    rw [← selectedEq, checkpoint.compiled.rankEq, atEnd]
  have addresses : setup.recoveryAddressWord sourceTrace =
      control.execution.application.sourceCurrentAddressWord plan event.val := by
    rw [numeric, witness.chronology.addresses]
    simp only [PhaseRuntimeState.sourceCurrentAddressWord, eventRank, Nat.add_sub_cancel_left]
  have committing : ProtocolState.atCommit setup.program source.point = true := by
    rw [installedSource]
    change ProtocolState.atCommit setup.program (checkpoint.residual.lift _) = true
    rw [checkpoint.atCommit, atCommit_cast reconstruct]
    rw [(earlier.liftPoint_recovery _).2.2.1]
    rfl
  have decodedOwner := decoded who request.2.2.2.2
  rw [selectedEq] at decodedOwner
  have observedPosition := decodeEventView?_position setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who event _ _ _ decodedOwner
  have rank : instructionCount setup.program -
      ProtocolState.remaining setup.program source.point = event.val := by
    have count := ProtocolView.position_add_remaining who setup.program source.point
    rw [observedPosition] at count
    omega
  refine ⟨source, sourceTrace, excluded, actor, committing, rank, ?_⟩
  intro observer active
  have view := decoded observer active
  rw [actualWord observer active, selectedEq] at view
  have observed : phaseSurvivingSourceView? setup .sequential runtime leaks observer event
      (control.execution.observe (phaseApplication runtime leaks) observer) =
        some (ProtocolState.observe observer setup.program source.point) := by
    rw [phaseSurvivingSourceView?_observed_of_history setup .sequential runtime leaks plan inputs
      horizon scheduler physicalTrace observer event]
    exact view
  unfold SourcePhaseClient.information?
  rw [observed, Option.bind_some]
  change setup.sourceInformation? observer
    (ProtocolState.observe observer setup.program source.point)
    (SourcePhaseClient.currentAddresses setup event control.execution.application.publicView) = _
  rw [SourcePhaseClient.currentAddresses_binding_read setup control.execution.application event
    who payload binding, ← addresses]
  exact setup.sourceInformation?_of_history observer source sourceTrace (by rwa [excluded])

/-- One factual source cursor serves every survivor's original information
and every possible original policy at the actual first binding callback. -/
theorem phase_first_binding_policy_of_current_information
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (serviceGraph setup .sequential))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup .sequential)))
    (bounds : MessageBounds (serviceGraph setup .sequential))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (SourcePhaseClient.initial setup runtime leaks) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .sequential).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks who
      ⟨control.execution.application.attempt, event⟩ (control.execution.recall who)) :
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.current.excluded ∧
      (∀ observer, observer ∉ control.execution.application.current.excluded →
        SourcePhaseClient.information? setup runtime leaks observer event
            (control.execution.observe (phaseApplication runtime leaks) observer) =
          some (setup.commitRecoveryModel.infoOf observer sourceTrace)) ∧
      ∀ policy : setup.commitRecoveryModel.BehavioralPolicy who,
        SourcePhaseClient.policy setup runtime leaks bounds who policy
            (control.execution.recall who)
            (control.execution.observe (phaseApplication runtime leaks) who) =
          (policy (setup.commitRecoveryModel.infoOf who sourceTrace)).bind fun choice =>
            SourcePhaseClient.moveResponse setup runtime leaks bounds who event choice.val
              (control.execution.recall who)
              (control.execution.observe (phaseApplication runtime leaks) who) := by
  obtain ⟨source, sourceTrace, excluded, _actor, _committing, _rank, information⟩ :=
    phase_ready_binding_current_information setup runtime leaks horizon scheduler trace who event
      payload binding request
  have actualTrace : ((phaseApplication runtime leaks).protocol
      ((setup.initialLaw.map encodeInputs).map
        (PhaseRuntimeState.initial (SourcePhaseClient.plan setup)))
      horizon scheduler).Trace (some control) := by
    rw [PMF.map_comp]
    exact trace
  obtain ⟨inputs, valid⟩ := phaseNativeInvariant_history runtime leaks
    (SourcePhaseClient.plan setup) (setup.initialLaw.map encodeInputs) horizon scheduler actualTrace
  refine ⟨source, sourceTrace, excluded, information, ?_⟩
  intro policy
  exact SourcePhaseClient.policy_first setup runtime leaks bounds who policy event _ _
    (requestedEvent_of_request setup .sequential _ valid who event request)
    first _ (information who request.2.2.2.2)

end Vegas
