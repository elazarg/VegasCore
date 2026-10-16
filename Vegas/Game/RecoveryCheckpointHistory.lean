/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedNormalization
import Vegas.Game.RecoveryArchivedInitialization
import Vegas.Game.RecoveryInitialCheckpoint
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseRawCheckpoint
import Vegas.Pending.PhaseHistoryCheckpoint
import Interaction.ReactiveInvariant

/-! # Actual initialized phased histories have reachable typed source checkpoints -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem phase_source_invariant
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      (∃ checkpoint : RecoverySourceCheckpoint setup mode state,
        checkpoint.ArchivedRecall ∧
        ∃ sourceTrace : setup.commitRecoveryProtocol.Trace
          (some (CommitRecoveryState.atPoint
            (checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
            state.entry.excluded state.generation)),
          ArchivedSourceOrigins setup mode state.retired ⟨_, sourceTrace⟩) ∧
      (∃ inputs, state.Invariant inputs) ∧ state.BindingRecord ∧ state.ReceiptRecord ∧
      state.StoredCheckpoint ∧ state.HistoryCheckpoint ∧ state.PublicFailureOrder ∧
      state.phases <:+ plan.phases ∧ state.ArchivesBefore) := by
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  refine ⟨?_, ?_, ?_⟩
  · intro state who material valid
    obtain ⟨⟨checkpoint, aligned, sourceTrace, sourceOrigins⟩, ⟨inputs, native⟩, binding, receipts,
      stored, remembered,
      order, suffix, archives⟩ := valid
    exact ⟨⟨checkpoint.transfer rfl rfl rfl, aligned, sourceTrace, sourceOrigins⟩,
      ⟨inputs, (phaseApplication_invariant runtime leaks inputs).submit state who material native⟩,
      (phaseApplication_bindingInvariant runtime leaks).submit state who material binding,
      (phaseApplication_receiptRecord runtime leaks graphOrder).submit state who material receipts,
      (phaseApplication_storedCheckpoint runtime leaks).submit state who material stored,
      (phaseApplication_historyCheckpoint runtime leaks).submit state who material remembered,
      (phaseApplication_publicFailureOrder graphOrder runtime leaks).submit state who material
        order,
      (phaseApplication_planSuffix runtime leaks plan).submit state who material suffix, archives⟩
  · intro state message next valid accepted
    obtain ⟨⟨checkpoint, aligned, sourceTrace, sourceOrigins⟩, ⟨inputs, native⟩, binding, receipts,
      stored, remembered,
      order, suffix, archives⟩ := valid
    refine ⟨?_,
      ⟨inputs, (phaseApplication_invariant runtime leaks inputs).handle state message next native
        accepted⟩,
      (phaseApplication_bindingInvariant runtime leaks).handle state message next binding accepted,
      (phaseApplication_receiptRecord runtime leaks graphOrder).handle state message next receipts
        accepted,
      (phaseApplication_storedCheckpoint runtime leaks).handle state message next stored accepted,
      (phaseApplication_historyCheckpoint runtime leaks).handle state message next remembered
        accepted,
      (phaseApplication_publicFailureOrder graphOrder runtime leaks).handle state message next order
        accepted,
      (phaseApplication_planSuffix runtime leaks plan).handle state message next suffix accepted,
      ((PhaseRuntimeState.archivesBefore_invariant runtime leaks).handle state message next
        ⟨order.frontier.adjacent, archives⟩ accepted).2⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨result, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      let nativeMessage : Message Player
          (Payload ((toEventGraph setup.program).withMode mode)) :=
        ⟨message.id, message.payload.packet.call⟩
      let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
        { state with current := state.current.inclusionResult message.payload.packet.call result }
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      have permitted : state.current.excludedCall message.payload.packet.call = false := by
        cases flag : state.current.excludedCall message.payload.packet.call with
        | false => rfl
        | true =>
            have negative := (Bool.and_eq_true_iff.mp allowed).2
            rw [flag] at negative
            cases negative
      let rawCheckpoint : RecoverySourceCheckpoint setup mode raw :=
        checkpoint.transfer rfl rfl rfl
      have rawNative : raw.Invariant inputs :=
        ⟨native.saved, handle_invariant runtime _ result nativeMessage native.active handled⟩
      have rawBinding := binding.inclusionResult runtime state nativeMessage result handled
      have rawReceipts := receipts.inclusionResult runtime state nativeMessage result authorized
        permitted handled graphOrder
      have rawStored := stored.inclusionResult runtime state nativeMessage result handled
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
      have rawAligned : rawCheckpoint.ArchivedRecall := by
        simpa only [rawCheckpoint, RecoverySourceCheckpoint.transfer,
          RecoverySourceCheckpoint.ArchivedRecall, raw] using aligned
      obtain ⟨nextCheckpoint, nextAligned, nextTrace, _fuel, _sourcePath, nextOrigins⟩ :=
        rawCheckpoint.normalized_archived raw sourceTrace rawAligned sourceOrigins
          archives rawNative rawBinding rawReceipts rawStored rawRemembered rawOrder
          (plan.suffix_geometry maximal state.phases suffix).2.2
      exact ⟨nextCheckpoint, nextAligned, nextTrace, nextOrigins⟩
    · cases accepted
  · intro state command next valid reached
    obtain ⟨⟨checkpoint, aligned, sourceTrace, sourceOrigins⟩, ⟨inputs, native⟩, binding, receipts,
      stored, remembered,
      order, suffix, archives⟩ := valid
    refine ⟨?_,
      ⟨inputs, (phaseApplication_invariant runtime leaks inputs).environment state command next
        native reached⟩,
      (phaseApplication_bindingInvariant runtime leaks).environment state command next binding
        reached,
      (phaseApplication_receiptRecord runtime leaks graphOrder).environment state command next
        receipts reached,
      (phaseApplication_storedCheckpoint runtime leaks).environment state command next stored
        reached,
      (phaseApplication_historyCheckpoint runtime leaks).environment state command next remembered
        reached,
      (phaseApplication_publicFailureOrder graphOrder runtime leaks).environment state command next
        order reached,
      (phaseApplication_planSuffix runtime leaks plan).environment state command next suffix
        reached,
      ((PhaseRuntimeState.archivesBefore_invariant runtime leaks).environment state command next
        ⟨order.frontier.adjacent, archives⟩ reached).2⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i authorized
      obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
        { state with current := state.current.environmentResult command result }
      let rawCheckpoint : RecoverySourceCheckpoint setup mode raw :=
        checkpoint.transfer rfl rfl rfl
      have rawNative : raw.Invariant inputs :=
        ⟨native.saved,
          environmentStep_invariant runtime _ result command native.active supported⟩
      have rawBinding := binding.environmentResult runtime state command result supported
      have rawReceipts := receipts.environmentResult runtime state command result authorized
        supported
      have rawStored := stored.environmentResult runtime state command result supported
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
      have rawAligned : rawCheckpoint.ArchivedRecall := by
        simpa only [rawCheckpoint, RecoverySourceCheckpoint.transfer,
          RecoverySourceCheckpoint.ArchivedRecall, raw] using aligned
      obtain ⟨nextCheckpoint, nextAligned, nextTrace, _fuel, _sourcePath, nextOrigins⟩ :=
        rawCheckpoint.normalized_archived raw sourceTrace rawAligned sourceOrigins
          archives rawNative rawBinding rawReceipts rawStored rawRemembered rawOrder
          (plan.suffix_geometry maximal state.phases suffix).2.2
      exact ⟨nextCheckpoint, nextAligned, nextTrace, nextOrigins⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact ⟨checkpoint, aligned, sourceTrace, sourceOrigins⟩

/-- Every actual initialized phased history has a saved typed source
checkpoint reached in the actual auxiliary recovery protocol. This includes
arbitrary legal player behavior, native schedules and every reset. No source
path, source outcome, exclusion agreement or simulation witness is assumed. -/
theorem recoverySourceCheckpoint_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control)) :
    ∃ checkpoint : RecoverySourceCheckpoint setup mode control.execution.application,
      checkpoint.ArchivedRecall ∧
      ∃ sourceTrace : setup.commitRecoveryProtocol.Trace
        (some (CommitRecoveryState.atPoint
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
          control.execution.application.entry.excluded control.execution.application.generation)),
        ArchivedSourceOrigins setup mode control.execution.application.retired
          ⟨_, sourceTrace⟩ := by
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  have invariant := phase_source_invariant setup mode runtime leaks plan maximal
  have valid := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · exact valid.1
  · obtain ⟨draw, drawSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    refine ⟨⟨RecoverySourceCheckpoint.initialized setup mode plan draw drawSupport,
        RecoverySourceCheckpoint.initialized_archived setup mode plan draw drawSupport,
        Classical.choice
          (RecoverySourceCheckpoint.initialized setup mode plan draw drawSupport).trace,
        ?_⟩,
      ⟨encodeInputs draw, (PhaseRuntimeState.initial_invariant plan (encodeInputs draw)).1⟩,
      PhaseRuntimeState.initial_bindingRecord plan (encodeInputs draw),
      PhaseRuntimeState.initial_receiptRecord plan (encodeInputs draw),
      PhaseRuntimeState.initial_storedCheckpoint plan (encodeInputs draw),
      PhaseRuntimeState.initial_historyCheckpoint plan (encodeInputs draw),
      PhaseRuntimeState.initial_publicFailureOrder graphOrder plan (encodeInputs draw),
      PhaseRuntimeState.settle_suffix _ _ _ _ _,
      PhaseRuntimeState.settle_archivesBefore _ _ _ _ _ plan.adjacent
        (fun _ impossible => by cases impossible)⟩
    intro index bound
    rw [phaseInitial_eq_raw] at bound
    exact (Nat.not_lt_zero index bound).elim

end Vegas
