/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryBindingCounterpart
import Vegas.Game.RecoveryCheckpointHistory
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseLive

/-! # Source decision witnesses from actual initialized phased binding histories -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every actual clear ready binding has a genuine auxiliary source trace
with the same decoded whole private view. The saved checkpoint, its typed
prefix, and exact action-history alignment are all derived from the history. -/
theorem phase_ready_binding_sourceView
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
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (clear : control.execution.application.current.excluded = ∅) :
    ∃ (source : CommitRecoveryState setup.program)
      (_trace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = ∅ ∧ source.generation = control.execution.application.generation ∧
      ProtocolState.actor setup.program source.point = some who ∧
      phaseSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) =
          some (ProtocolState.observe who setup.program source.point) := by
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨checkpoint⟩ := recoverySourceCheckpoint_history setup mode runtime leaks plan maximal
    horizon scheduler trace
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have bindingRecord := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have retained := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have live := (phaseApplication_live runtime leaks).history
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler (fun state member => by
      obtain ⟨initial, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact ⟨PhaseRuntimeState.initial_frontier plan initial,
        PhaseRuntimeState.initial_live plan initial⟩) physicalTrace
  have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
    physicalTrace
  have savedClear : control.execution.application.entry.excluded = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro owner excluded
    have current := coverage.inherited excluded
    rw [clear] at current
    exact Finset.notMem_empty _ current
  cases installed : control.execution.application.phases with
  | nil =>
      have terminal := exclusion.frontier.terminal installed
      exact (ready.1 (terminal.symm ▸ Finset.mem_univ event)).elim
  | cons phase remaining =>
      have head : phase ∈ control.execution.application.phases.head? := by
        rw [installed]
        exact Option.mem_some_iff.mpr rfl
      have position := exclusion.frontier.positioned
      rw [installed] at position
      rw [installed] at geometry
      have boundaries := PhaseRuntimeState.phase_boundaries phase remaining geometry.1
        geometry.2.1 geometry.2.2
      have inside := phase.ready_mem control.execution.application.current
        (serviceGraph_revealRelaxedOrdered setup mode) position.2 (live.2 phase head)
        boundaries.1 boundaries.2 event ready
      have typed := phase.fields event ((phase.mem_events event).mp inside).1
        ((phase.mem_events event).mp inside).2
      have kind : phase.kind = .commitment := by
        cases kind : phase.kind with
        | commitment => rfl
        | reveal =>
            rw [kind] at typed
            obtain ⟨value, layout⟩ := typed
            rw [binding] at layout
            cases layout
        | sample =>
            rw [kind] at typed
            obtain ⟨value, layout⟩ := typed
            rw [binding] at layout
            cases layout
      exact checkpoint.ready_binding_sourceView runtime leaks control.execution exclusion.frontier
        stored retained phase remaining installed kind event inside ready who payload binding
        savedClear bindingRecord.active native.active.reachable

/-- A classified actual intended-view witness realizes the complete source
information used by the physical component; fallback views are not declared played. -/
theorem phase_ready_binding_information
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
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (clear : control.execution.application.current.excluded = ∅)
    (wellFormed : setup.WellFormed) (original : setup.intendedProtocol.History)
    (same : phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who) =
        setup.intendedModel.infoOf who original.trace) :
    setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who))) := by
  obtain ⟨source, sourceTrace, excluded, _generation, actor, decoded⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler trace
      who event payload binding ready clear
  rw [same]
  exact commitRecovery_isDecisionInfo_of_clear_view setup wellFormed who source sourceTrace
    excluded actor original (decoded.symm.trans same)

end Vegas
