/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySurvivingBindingSource
import Vegas.Game.RecoveryArchivedBindingRecall
import Vegas.Game.RecoveryCheckpointHistory
import Vegas.Pending.PhaseBindingReadiness

/-! # Initialized surviving binding source witnesses after exclusions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every initialized surviving ready binding has a genuine played auxiliary
source decision with the saved source exclusions and actual generation.
Current physical exclusions may additionally contain in-phase failures.
The full source own word is identified with all actual archived and current
owned native actions. A parser of the retained physical recall is separate. -/
theorem RecoverySourceCheckpoint.surviving_binding_source
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (archivedRecall : checkpoint.ArchivedRecall)
    (publicChronology : checkpoint.PublicChronology plan)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.entry.excluded ∧
      source.generation = control.execution.application.generation ∧
      setup.commitRecoveryPublic (some source) =
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase) ∧
      ProtocolState.actor setup.program source.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      ProtocolState.history setup.program source.point who =
        decodeHistory setup.program
          ((PhaseRuntimeState.archivedHistory control.execution.application.retired
            control.execution.application.current.native.config.history).map
              ((toEventGraph setup.program).fromModeCompletion mode)) who ∧
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who event
        ((serviceGraph setup mode).playerStore who
          control.execution.application.current.native.config.store)
        (ProtocolState.history setup.program source.point who) =
          some (ProtocolState.observe who setup.program source.point) ∧
      setup.recoveryAddressWord sourceTrace =
        control.execution.application.sourcePublicAddressWord plan event.val ∧
      (∀ (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) observer,
        setup.proposalRecoveryArchive observer (setup.proposalRecoveryModel.infoOf observer
            (setup.proposalRecoveryLiftTrace labels sourceTrace)) =
          setup.proposalRecoveryArchive observer (setup.proposalRecoveryModel.infoOf observer
            (setup.proposalRecoveryLiftTrace labels checkpoint.trace))) := by
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
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
  obtain ⟨_input, native⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have archives := PhaseRuntimeState.archivesBefore_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have survives : who ∉ control.execution.application.entry.excluded :=
    fun member => request.2.2.2.2 (coverage.inherited member)
  obtain ⟨phase, remaining, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
      physicalTrace who event payload binding request.2.2.1
  obtain ⟨selected, selectedEq, Δ, P, name, fresh, guard, next, earlier, atEnd, reconstruct⟩ :=
    checkpoint.ready_binding_prefix exclusion.frontier phase remaining installed kind event inside
      request.2.2.1 who payload binding
  have acting : (serviceGraph setup mode).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding _ binding
  have notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication := by
    rw [binding]
    exact id
  obtain ⟨source, sourceTrace, excluded, generation, publicSignal, sourceActor, played,
      word, decoded, numeric, proposalArchive⟩ :=
    checkpoint.surviving_prefix_trace fresh guard next earlier reconstruct stored survives selected
      atEnd (selectedEq.symm ▸ request.2.2.1) (selectedEq.symm ▸ acting)
      (selectedEq.symm ▸ notPublication)
  have saved : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase := by
    have positioned := exclusion.frontier.positioned
    rw [installed] at positioned
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using positioned.1
  have actualWord := checkpoint.filled_prefix_archived_history_of_ready archivedRecall archives
    fresh guard next earlier reconstruct survives selected atEnd (selectedEq.symm ▸ request.2.2.1)
      (selectedEq.symm ▸ acting) bindingRecord.active native.active.reachable retained saved
  rw [word, selectedEq] at decoded
  have archiveExclusions := phaseArchivedExclusions_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have savedFailures := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have savedExcluded := PhaseRuntimeState.saved_excluded_eq_public_failures archiveExclusions
    savedFailures exclusion.frontier phase remaining installed
  have eventRank : event.val = control.execution.application.attempt.phase + earlier.length := by
    rw [← selectedEq, checkpoint.compiled.rankEq, atEnd]
  refine ⟨source, sourceTrace, excluded, generation, publicSignal, sourceActor, played,
    word.symm.trans actualWord, decoded, ?_, proposalArchive⟩
  rw [numeric, publicChronology.addresses,
    PhaseRuntimeState.sourcePublicAddressWord_saved]
  dsimp only [PhaseRuntimeState.sourcePublicAddressWord, State.sourceFailureFootprint]
  have failures := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords
    control.execution.application.retired
  unfold RuntimePhasePlan.sourceRecordFailures at failures
  rw [eventRank, Nat.add_sub_cancel_left, failures, ← savedExcluded]
  rfl

/-- Every initialized raw binding request has the actual surviving source counterpart. -/
theorem phase_ready_binding_surviving_source
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.entry.excluded ∧
      source.generation = control.execution.application.generation ∧
      setup.commitRecoveryPublic (some source) =
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase) ∧
      ProtocolState.actor setup.program source.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      ProtocolState.history setup.program source.point who =
        decodeHistory setup.program
          ((PhaseRuntimeState.archivedHistory control.execution.application.retired
            control.execution.application.current.native.config.history).map
              ((toEventGraph setup.program).fromModeCompletion mode)) who ∧
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who event
        ((serviceGraph setup mode).playerStore who
          control.execution.application.current.native.config.store)
        (ProtocolState.history setup.program source.point who) =
          some (ProtocolState.observe who setup.program source.point) ∧
      setup.recoveryAddressWord sourceTrace =
        control.execution.application.sourcePublicAddressWord plan event.val := by
  obtain ⟨checkpoint, archivedRecall, publicChronology, _sourceOrigin⟩ :=
    recoverySourceCheckpoint_history setup mode runtime leaks plan maximal horizon scheduler trace
  obtain ⟨source, sourceTrace, excluded, generation, publicSignal, actor, played, word, decoded,
    numeric, _proposalArchive⟩ :=
    RecoverySourceCheckpoint.surviving_binding_source setup mode runtime leaks plan maximal horizon
      scheduler trace checkpoint archivedRecall publicChronology who event payload binding request
  exact ⟨source, sourceTrace, excluded, generation, publicSignal, actor, played, word, decoded,
    numeric⟩

end Vegas
