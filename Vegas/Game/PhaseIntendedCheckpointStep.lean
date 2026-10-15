/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRawCommitAdmission
import Vegas.Game.RecoveryIntendedNormalization
import Vegas.Pending.PhaseRawCheckpoint
import Vegas.Pending.PhaseHistoryCheckpoint

/-! # Chosen intended source checkpoints through actual clear physical operations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan) inputs

include source copies maximal

/-- An actual accepted envelope preserves whole intendedness at one chosen
successor checkpoint. Admission is reconstructed at the old checkpoint before
the completed physical phase is normalized. -/
theorem phase_handle_intended_checkpoint
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (intended : ProtocolState.Intended setup.program (checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup mode)))
    (authentic : message ∈ control.execution.network.inputs)
    (next : PhaseRuntimeState (serviceGraph setup mode))
    (accepted : (app).handle control.execution.application message = some next)
    (nextClear : next.current.excluded = ∅) :
    ∃ chosen : RecoverySourceCheckpoint setup mode next,
      ProtocolState.Intended setup.program (chosen.residual.lift
        (ProtocolState.entry chosen.residual.tail chosen.source)) := by
  let state := control.execution.application
  have rawTrace := (menu).toRawTrace initial horizon scheduler trace
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    rawTrace
  have remembered := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    rawTrace
  have order := phasePublicFailureOrder_history runtime leaks graphOrder plan inputs horizon
    scheduler rawTrace
  have geometry := (phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
    rawTrace).2.2
  change state.handle runtime message = some next at accepted
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · rename_i allowed
    obtain ⟨result, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    let nativeMessage : Message Player (Payload (serviceGraph setup mode)) :=
      ⟨message.id, message.payload.packet.call⟩
    let raw : PhaseRuntimeState (serviceGraph setup mode) :=
      { state with current := state.current.inclusionResult message.payload.packet.call result }
    have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
    have current : message.payload.attempt = state.attempt := by
      have valid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).1
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp valid).1
    have permitted : state.current.excludedCall message.payload.packet.call = false := by
      cases flag : state.current.excludedCall message.payload.packet.call with
      | false => rfl
      | true =>
          have negative := (Bool.and_eq_true_iff.mp allowed).2
          rw [flag] at negative
          cases negative
    have unchanged := raw.normalize_of_clear nextClear
    have rawClear : raw.current.excluded = ∅ :=
      (congrArg RecoveryState.excluded unchanged.1).symm.trans nextClear
    obtain ⟨binding, stored, receipts⟩ := phase_inclusion_checkpoint_history runtime leaks
      graphOrder plan inputs horizon scheduler rawTrace nativeMessage result authorized permitted
        handled
    have rawNative : raw.Invariant draw :=
      ⟨native.saved, handle_invariant runtime _ result nativeMessage native.active handled⟩
    have rawRemembered : raw.HistoryCheckpoint := by
      obtain ⟨event, _named, ready, action, supported⟩ :=
        handle_config_mem_step runtime _ result nativeMessage handled
      apply remembered.trans
      change state.current.native.config.history.IsPrefix result.config.history
      rw [state.current.native.config.step_history _ _ _ _ supported]
      exact ⟨_, rfl⟩
    have rawOrder : raw.PublicFailureOrder :=
      ⟨state.raw_handle_frontier runtime order.frontier nativeMessage result authorized handled,
        ⟨order.coverage.saved, order.coverage.active.inclusionResult runtime nativeMessage result
            handled,
          order.coverage.inherited.trans (state.current.inclusionResult_excluded_subset _ _)⟩,
        fun phase member => (order.publicationOrder phase member).inclusionResult
          order.coverage.active order.coverage.inherited graphOrder runtime nativeMessage result
            permitted handled⟩
    let transferred : RecoverySourceCheckpoint setup mode raw := checkpoint.transfer rfl rfl rfl
    exact transferred.normalized_intended raw rawNative binding receipts
      stored rawRemembered rawOrder geometry rawClear intended (by
        intro phase remaining installed finished committing
        exact phase_handle_commit_admitted setup mode runtime leaks bounds wellFormed source
          assessment copies plan maximal inputs horizon scheduler trace clear checkpoint message
            authentic current result handled rawClear committing phase remaining installed
              consistent intended finished)
  · cases accepted

/-- Each actual supported application command preserves whole intendedness at
the chosen source successor. Clock, sample and expiry outcomes share the same
physical normalization argument. -/
theorem phase_environment_intended_checkpoint
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (intended : ProtocolState.Intended setup.program (checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (command : EnvironmentCommand (serviceGraph setup mode))
    (next : PhaseRuntimeState (serviceGraph setup mode))
    (reached : next ∈ ((app).environment control.execution.application command).support)
    (nextClear : next.current.excluded = ∅) :
    ∃ chosen : RecoverySourceCheckpoint setup mode next,
      ProtocolState.Intended setup.program (chosen.residual.lift
        (ProtocolState.entry chosen.residual.tail chosen.source)) := by
  let state := control.execution.application
  have rawTrace := (menu).toRawTrace initial horizon scheduler trace
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    rawTrace
  have remembered := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    rawTrace
  have order := phasePublicFailureOrder_history runtime leaks graphOrder plan inputs horizon
    scheduler rawTrace
  have geometry := (phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
    rawTrace).2.2
  change next ∈ (state.environment runtime command).support at reached
  unfold PhaseRuntimeState.environment at reached
  split at reached
  · rename_i authorized
    obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
    let raw : PhaseRuntimeState (serviceGraph setup mode) :=
      { state with current := state.current.environmentResult command result }
    have unchanged := raw.normalize_of_clear nextClear
    have rawClear : raw.current.excluded = ∅ :=
      (congrArg RecoveryState.excluded unchanged.1).symm.trans nextClear
    obtain ⟨binding, stored, receipts⟩ := phase_environment_checkpoint_history runtime leaks
      graphOrder plan inputs horizon scheduler rawTrace command result authorized supported
    have rawNative : raw.Invariant draw :=
      ⟨native.saved, environmentStep_invariant runtime _ result command native.active supported⟩
    have rawRemembered : raw.HistoryCheckpoint :=
      remembered.trans (environmentStep_history_prefix runtime _ result command supported)
    have rawOrder : raw.PublicFailureOrder :=
      ⟨state.raw_environment_frontier runtime order.frontier command result authorized supported,
        ⟨order.coverage.saved, order.coverage.active.environmentResult runtime command result
            supported,
          order.coverage.inherited.trans (state.current.environmentResult_excluded_subset _ _)⟩,
        fun phase member => (order.publicationOrder phase member).environmentResult
          order.coverage.active order.coverage.inherited graphOrder runtime command result
            supported⟩
    let transferred : RecoverySourceCheckpoint setup mode raw := checkpoint.transfer rfl rfl rfl
    exact transferred.normalized_intended raw rawNative binding receipts
      stored rawRemembered rawOrder geometry rawClear intended (by
        intro phase remaining installed finished committing
        exact phase_environment_commit_admitted setup mode runtime leaks bounds wellFormed source
          assessment copies plan maximal inputs horizon scheduler trace clear checkpoint command
            result supported rawClear committing phase remaining installed consistent intended
              finished)
  · have unchanged : next = control.execution.application :=
      (PMF.mem_support_pure_iff _ _).mp reached
    subst next
    exact ⟨checkpoint, intended⟩

end Vegas
