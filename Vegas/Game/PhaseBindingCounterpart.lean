/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryBindingCounterpart
import Vegas.Game.RecoveryCheckpointHistory
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingReadiness
import Vegas.Game.CommitRecoveryClearDecoder

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
  obtain ⟨checkpoint, _archivedRecall, _sourceOrigin⟩ :=
    recoverySourceCheckpoint_history setup mode runtime leaks plan maximal
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
  have savedClear : control.execution.application.entry.excluded = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro owner excluded
    have current := coverage.inherited excluded
    rw [clear] at current
    exact Finset.notMem_empty _ current
  obtain ⟨phase, remaining, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
      physicalTrace who event payload binding ready
  exact checkpoint.ready_binding_sourceView runtime leaks control.execution exclusion.frontier
    stored retained phase remaining installed kind event inside ready who payload binding
    savedClear bindingRecord.active native.active.reachable

/-- Every actual clear ready binding realizes the complete auxiliary source
information selected by the physical decoder, including signal and own-play recall. -/
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
    (wellFormed : setup.WellFormed) :
    setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who))) := by
  obtain ⟨source, sourceTrace, excluded, _generation, actor, decoded⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler trace
      who event payload binding ready clear
  have played := commitRecovery_isDecisionInfo_of_actor setup source sourceTrace who
    excluded actor
  have observed := setup.commitRecoveryClearInformation_observed wellFormed who sourceTrace
    excluded
  rw [observed] at played
  rw [decoded]
  exact played

end Vegas
