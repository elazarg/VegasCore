/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedNormalization
import Vegas.Game.RecoveryArchivedInitialization
import Vegas.Game.RecoveryInitialCheckpoint
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseRawCheckpoint
import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Pending.PhaseCountProjection

/-! # Shared chosen source witnesses for actual application transitions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The existing native and source invariants, with the chosen source trace
retained as data. Raw existence and counted archive tracking use the same
transition producers on this witness. -/
structure RecoverySourceWitness
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)) where
  checkpoint : RecoverySourceCheckpoint setup mode state
  aligned : checkpoint.ArchivedRecall
  chronology : checkpoint.PublicChronology plan
  origins : ArchivedSourceOrigins setup mode state.retired ⟨_, checkpoint.trace⟩
  native : ∃ inputs, state.Invariant inputs
  binding : state.BindingRecord
  receipts : state.ReceiptRecord
  stored : state.StoredCheckpoint
  remembered : state.HistoryCheckpoint
  order : state.PublicFailureOrder
  suffix : state.phases <:+ plan.phases
  archives : state.ArchivesBefore
  exclusions : state.ArchivedExclusions
  failures : state.PublicFailureCheckpoint

namespace RecoverySourceWitness

variable {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
  {plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode)}
  {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}

/-- A real submission preserves the same chosen source trace, including its
private old word, while registering the actual witnessed material. -/
def submit (witness : RecoverySourceWitness setup mode plan state)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (owner : Player) (material : WitnessedSubmission ((toEventGraph setup.program).withMode mode)) :
    RecoverySourceWitness setup mode plan (state.submit owner material) := by
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  refine {
    checkpoint := witness.checkpoint.transfer rfl rfl rfl
    aligned := witness.aligned
    chronology := ?_
    origins := witness.origins
    native := ?_
    binding := (phaseApplication_bindingInvariant runtime leaks).submit _ _ _ witness.binding
    receipts := (phaseApplication_receiptRecord runtime leaks graphOrder).submit _ _ _
      witness.receipts
    stored := (phaseApplication_storedCheckpoint runtime leaks).submit _ _ _ witness.stored
    remembered := (phaseApplication_historyCheckpoint runtime leaks).submit _ _ _ witness.remembered
    order := (phaseApplication_publicFailureOrder graphOrder runtime leaks).submit _ _ _
      witness.order
    suffix := (phaseApplication_planSuffix runtime leaks plan).submit _ _ _ witness.suffix
    archives := witness.archives
    exclusions := (phaseApplication_archivedExclusions runtime leaks).submit _ _ _
      witness.exclusions
    failures := (phaseApplication_publicFailureCheckpoint runtime leaks).submit _ _ _
      witness.failures
  }
  · refine ⟨?_, witness.chronology.consumed⟩
    change setup.recoveryAddressWord witness.checkpoint.trace = _
    exact witness.chronology.addresses.trans
      (PhaseRuntimeState.sourcePublicAddressWord_congr plan
        (PhaseCount.submit_publicView state owner material).symm state.attempt.phase)
  · obtain ⟨inputs, native⟩ := witness.native
    exact ⟨inputs, (phaseApplication_invariant runtime leaks inputs).submit _ _ _ native⟩

/-- Native inclusion and the subsequent real normalizer choose one shared
checkpoint. The returned proposal increment is derived on its exact trace. -/
theorem after_handle (witness : RecoverySourceWitness setup mode plan state)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (message : Message Player (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (result : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (allowed : (message.payload.tokenValid state.attempt && state.allows
      message.payload.packet.call &&
      !state.current.excludedCall message.payload.packet.call) = true)
    (handled : EventGraphRuntime.handle runtime state.current.native
      ⟨message.id, message.payload.packet.call⟩ = some result) :
    let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
      { state with current := state.current.inclusionResult message.payload.packet.call result }
    ∃ next : RecoverySourceWitness setup mode plan raw.normalize,
      (witness.checkpoint.transfer (other := raw) rfl rfl rfl).ProposalDelta plan
        next.checkpoint := by
  dsimp only
  obtain ⟨inputs, native⟩ := witness.native
  let checkpoint := witness.checkpoint
  have aligned := witness.aligned
  have chronology := witness.chronology
  have sourceOrigins := witness.origins
  have binding := witness.binding
  have receipts := witness.receipts
  have stored := witness.stored
  have remembered := witness.remembered
  have order := witness.order
  have suffix := witness.suffix
  have archives := witness.archives
  have archiveExclusions := witness.exclusions
  have savedFailures := witness.failures
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
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
  have rawExtension : state.current.native.PublicFailureExtension raw.current.native :=
    (completionStep_handle runtime _ result nativeMessage handled).publicFailureExtension
  have rawSavedFailures : raw.PublicFailureCheckpoint := savedFailures.trans rawExtension
  have rawArchiveExclusions : raw.ArchivedExclusions :=
    ⟨rawOrder.coverage, archiveExclusions.saved,
      archiveExclusions.active.inclusionResult runtime nativeMessage result handled⟩
  have rawChronology : rawCheckpoint.PublicChronology plan := by
    apply RecoverySourceCheckpoint.PublicChronology.current checkpoint plan chronology
      raw.current rawExtension
    have positioned := order.frontier.positioned
    cases installed : state.phases with
    | nil =>
        rw [installed] at positioned
        intro event _
        exact (positioned.2 event).mpr event.isLt
    | cons phase remaining =>
        rw [installed] at positioned
        simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
          Option.getD_some] using positioned.2.1
  obtain ⟨nextCheckpoint, nextAligned, nextChronology, _fuel, _sourcePath, nextOrigins,
    proposalDelta⟩ :=
    rawCheckpoint.normalized_archived raw plan suffix rawChronology rawArchiveExclusions
      rawSavedFailures rawAligned sourceOrigins
      archives rawNative rawBinding rawReceipts rawStored rawRemembered rawOrder
      maximal
  have accepted : state.handle runtime message = some raw.normalize := by
    rw [PhaseRuntimeState.handle, ite_eq_left allowed, handled, Option.map_some]
  refine ⟨{
    checkpoint := nextCheckpoint
    aligned := nextAligned
    chronology := nextChronology
    origins := nextOrigins
    native := ⟨inputs, (phaseApplication_invariant runtime leaks inputs).handle _ _ _ native
      accepted⟩
    binding := (phaseApplication_bindingInvariant runtime leaks).handle _ _ _ binding accepted
    receipts := (phaseApplication_receiptRecord runtime leaks graphOrder).handle _ _ _ receipts
      accepted
    stored := (phaseApplication_storedCheckpoint runtime leaks).handle _ _ _ stored accepted
    remembered := (phaseApplication_historyCheckpoint runtime leaks).handle _ _ _ remembered
      accepted
    order := (phaseApplication_publicFailureOrder graphOrder runtime leaks).handle _ _ _
      order accepted
    suffix := (phaseApplication_planSuffix runtime leaks plan).handle _ _ _ suffix accepted
    archives := ((PhaseRuntimeState.archivesBefore_invariant runtime leaks).handle _ _ _
      ⟨order.frontier.adjacent, archives⟩ accepted).2
    exclusions := (phaseApplication_archivedExclusions runtime leaks).handle _ _ _ archiveExclusions
      accepted
    failures := (phaseApplication_publicFailureCheckpoint runtime leaks).handle _ _ _ savedFailures
      accepted
  }, proposalDelta⟩

/-- Environment processing retains its exact native result and the same
normalizer-selected source trace, including automatic phase advances. -/
theorem after_environment (witness : RecoverySourceWitness setup mode plan state)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (command : EnvironmentCommand ((toEventGraph setup.program).withMode mode))
    (result : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (authorized : state.commandAllowed command = true)
    (supported : result ∈ (environmentStep runtime state.current.native command).support) :
    let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
      { state with current := state.current.environmentResult command result }
    ∃ next : RecoverySourceWitness setup mode plan raw.normalize,
      (witness.checkpoint.transfer (other := raw) rfl rfl rfl).ProposalDelta plan
        next.checkpoint := by
  dsimp only
  obtain ⟨inputs, native⟩ := witness.native
  let checkpoint := witness.checkpoint
  have aligned := witness.aligned
  have chronology := witness.chronology
  have sourceOrigins := witness.origins
  have binding := witness.binding
  have receipts := witness.receipts
  have stored := witness.stored
  have remembered := witness.remembered
  have order := witness.order
  have suffix := witness.suffix
  have archives := witness.archives
  have archiveExclusions := witness.exclusions
  have savedFailures := witness.failures
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
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
  have rawExtension : state.current.native.PublicFailureExtension raw.current.native :=
    (completionStep_environmentStep runtime _ result command supported).publicFailureExtension
  have rawSavedFailures : raw.PublicFailureCheckpoint := savedFailures.trans rawExtension
  have rawArchiveExclusions : raw.ArchivedExclusions :=
    ⟨rawOrder.coverage, archiveExclusions.saved,
      archiveExclusions.active.environmentResult runtime command result supported⟩
  have rawChronology : rawCheckpoint.PublicChronology plan := by
    apply RecoverySourceCheckpoint.PublicChronology.current checkpoint plan chronology
      raw.current rawExtension
    have positioned := order.frontier.positioned
    cases installed : state.phases with
    | nil =>
        rw [installed] at positioned
        intro event _
        exact (positioned.2 event).mpr event.isLt
    | cons phase remaining =>
        rw [installed] at positioned
        simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
          Option.getD_some] using positioned.2.1
  obtain ⟨nextCheckpoint, nextAligned, nextChronology, _fuel, _sourcePath, nextOrigins,
    proposalDelta⟩ :=
    rawCheckpoint.normalized_archived raw plan suffix rawChronology rawArchiveExclusions
      rawSavedFailures rawAligned sourceOrigins
      archives rawNative rawBinding rawReceipts rawStored rawRemembered rawOrder
      maximal
  have reached : raw.normalize ∈ (state.environment runtime command).support := by
    rw [PhaseRuntimeState.environment, ite_eq_left authorized]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  refine ⟨{
    checkpoint := nextCheckpoint
    aligned := nextAligned
    chronology := nextChronology
    origins := nextOrigins
    native := ⟨inputs, (phaseApplication_invariant runtime leaks inputs).environment _ _ _
      native reached⟩
    binding := (phaseApplication_bindingInvariant runtime leaks).environment _ _ _ binding reached
    receipts := (phaseApplication_receiptRecord runtime leaks graphOrder).environment _ _ _ receipts
      reached
    stored := (phaseApplication_storedCheckpoint runtime leaks).environment _ _ _ stored reached
    remembered := (phaseApplication_historyCheckpoint runtime leaks).environment _ _ _ remembered
      reached
    order := (phaseApplication_publicFailureOrder graphOrder runtime leaks).environment _ _ _ order
      reached
    suffix := (phaseApplication_planSuffix runtime leaks plan).environment _ _ _ suffix reached
    archives := ((PhaseRuntimeState.archivesBefore_invariant runtime leaks).environment _ _ _
      ⟨order.frontier.adjacent, archives⟩ reached).2
    exclusions := (phaseApplication_archivedExclusions runtime leaks).environment _ _ _
      archiveExclusions
      reached
    failures := (phaseApplication_publicFailureCheckpoint runtime leaks).environment _ _ _
      savedFailures
      reached
  }, proposalDelta⟩

/-- The one supported setup draw initializes the same source witness used by
all later application transitions. No setup randomness is resampled. -/
def initialized (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
    RecoverySourceWitness setup mode plan (PhaseRuntimeState.initial plan (encodeInputs
      initial)) := by
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  refine {
    checkpoint := RecoverySourceCheckpoint.initialized setup mode plan initial supported
    aligned := RecoverySourceCheckpoint.initialized_archived setup mode plan initial supported
    chronology := RecoverySourceCheckpoint.initialized_publicChronology setup mode plan initial
      supported
    origins := ?_
    native := ⟨encodeInputs initial, (PhaseRuntimeState.initial_invariant plan (encodeInputs
      initial)).1⟩
    binding := PhaseRuntimeState.initial_bindingRecord plan (encodeInputs initial)
    receipts := PhaseRuntimeState.initial_receiptRecord plan (encodeInputs initial)
    stored := PhaseRuntimeState.initial_storedCheckpoint plan (encodeInputs initial)
    remembered := PhaseRuntimeState.initial_historyCheckpoint plan (encodeInputs initial)
    order := PhaseRuntimeState.initial_publicFailureOrder graphOrder plan (encodeInputs initial)
    suffix := PhaseRuntimeState.settle_suffix _ _ _ _ _
    archives := PhaseRuntimeState.settle_archivesBefore _ _ _ _ _ plan.adjacent
      (fun _ impossible => by cases impossible)
    exclusions := PhaseRuntimeState.initial_archivedExclusions plan (encodeInputs initial)
    failures := PhaseRuntimeState.initial_publicFailureCheckpoint plan (encodeInputs initial)
  }
  have noArchives : (PhaseRuntimeState.initial plan (encodeInputs initial)).retired = [] :=
    congrArg PhaseRuntimeState.retired (phaseInitial_eq_raw plan (encodeInputs initial))
  rw [noArchives]
  exact .initial plan initial supported

end RecoverySourceWitness
end Vegas
