/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOwnBindingFailure
import Vegas.Game.PhaseProposalHistory
import Vegas.Game.PhaseProposalSavedDebt

/-! # Observable saved binding failures force actual native checkpoint debt

The selector reads the player's ordinary view. Its semantic consequence uses
the SAME chosen archive-aligned checkpoint from the actual counted history.
Current-attempt failures are retained as a separate, cancelable case.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)

/-- An observed saved failure gives this actual chosen checkpoint's debt.
The actual current store may contain further failures or pending packets. -/
theorem RecoverySourceWitness.checkpointDebt_of_observed_saved_binding
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (witness : RecoverySourceWitness setup mode plan control.execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (failed : phaseProposalSavedBindingFailure setup mode runtime leaks who event
      (control.execution.observe app who)) : witness.CheckpointDebt who := by
  have stored := (phaseProposalSavedBindingFailure_iff_of_seed_request setup mode runtime leaks
    plan maximal horizon scheduler trace witness.checkpoint witness.aligned who event payload
      binding request).mp failed
  exact Or.inr (Or.inr stored)

/-- An actual unresolved failed saved FieldRef is visible to the selector.
Only the saved semantic cell is tested, not an unaccepted preparation. -/
theorem RecoverySourceWitness.observed_saved_binding_of_failed_cell
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (witness : RecoverySourceWitness setup mode plan control.execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    {name : VarId} {cellPayload : L.Ty}
    (cell : HasVar witness.checkpoint.residual.context name (.commitment who cellPayload))
    (unresolved : name ∈ witness.checkpoint.residual.names)
    (failed : (witness.checkpoint.refs.get cell).get?
      control.execution.application.entry.native.config.store = some .failure) :
    phaseProposalSavedBindingFailure setup mode runtime leaks who event
      (control.execution.observe app who) := by
  apply (phaseProposalSavedBindingFailure_iff_of_seed_request setup mode runtime leaks plan
    maximal horizon scheduler trace witness.checkpoint witness.aligned who event payload binding
      request).mpr
  have stored : witness.checkpoint.source.state.get cell = .failure :=
    Option.some.inj ((witness.checkpoint.agrees cell).symm.trans failed)
  have localFailure : witness.checkpoint.source.FailedBinding who
      witness.checkpoint.residual.names :=
    ⟨witness.checkpoint.unique, name, cellPayload, cell, unresolved, stored⟩
  exact witness.checkpoint.origin.failedBinding_lift who _
    (ProtocolState.failedBinding_entry _ _ localFailure)

/-- At every actual counted callback the observable selector supplies actual
saved debt. No checkpoint, archive or source-counterpart premise is supplied. -/
theorem phaseProposalSavedBindingFailure_checkpointDebt
    (bounds : MessageBounds (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (failed : phaseProposalSavedBindingFailure setup mode runtime leaks who event
      (control.execution.observe app who)) :
    PhaseCheckpointDebt setup mode plan who control.execution.application := by
  obtain ⟨witness, _archive⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler trace
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
    trace
  exact ⟨witness, RecoverySourceWitness.checkpointDebt_of_observed_saved_binding setup mode runtime
    leaks plan maximal horizon scheduler raw witness who event payload binding request failed⟩

omit [Fintype Player] in
/-- The current classifier is an actual original-source failure, with no
virtual replacement of unusable bindings. All source witnesses with this
typed readback agree on the failure by observation congruence. -/
theorem phaseProposalCurrentBindingFailure_genuine [Finite Player]
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (source : CommitRecoveryState setup.program)
      (_sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.entry.excluded ∧
      ProtocolState.actor setup.program source.point = some who ∧
      phaseSurvivingSourceView? setup mode runtime leaks who event
          (control.execution.observe app who) =
        some (ProtocolState.observe who setup.program source.point) ∧
      (phaseProposalCurrentBindingFailure setup mode runtime leaks who event
          (control.execution.observe app who) ↔
        ProtocolState.FailedBinding who setup.program source.point) := by
  obtain ⟨source, sourceTrace, excluded, _generation, _signal, actor, _played, readback⟩ :=
    phaseSurvivingSourceView?_of_ready_binding setup mode runtime leaks plan maximal horizon
      scheduler trace who event payload binding request
  exact ⟨source, sourceTrace, excluded, actor, readback,
    phaseProposalCurrentBindingFailure_iff_of_readback setup mode runtime leaks who event _
      source.point readback⟩

omit [Fintype Player] in
/-- The actual final raw instruction preserves existing current failure
before close. If that installed result finishes without a reset, the failure
becomes saved debt. The starting callback itself need not finish the block. -/
theorem phaseProposalCurrentBindingFailure_checkpointed_after_step
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : (app).PlayerView) (source : CommitRecoveryState setup.program)
    (readback : phaseSurvivingSourceView? setup mode runtime leaks who event view =
      some (ProtocolState.observe who setup.program source.point))
    (failed : phaseProposalCurrentBindingFailure setup mode runtime leaks who event view)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (result : SourceProgram.ProtocolState setup.program × Finset Player)
    (reached : result ∈ (ProtocolState.recoveryStep setup.program source.point source.excluded
      joint).support) :
    let pending := source.install result
      (ProtocolState.recoveryStep_excluded_monotone setup.program source.point source.excluded
        joint result reached)
    pending.Finished → ¬ pending.NewFailure →
      ProtocolState.OwesFailure who setup.program pending.close.saved ∧
        ProtocolState.OwesFailure who setup.program pending.close.point := by
  intro pending finished standing
  have before := (phaseProposalCurrentBindingFailure_iff_of_readback setup mode runtime leaks who
    event view source.point readback).mp failed
  have after := ProtocolState.failedBinding_recoveryStep who setup.program source.point
    source.excluded joint result before reached
  exact pending.close_checkpointed_owesFailure who finished standing (Or.inr after)

end Vegas
