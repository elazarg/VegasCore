/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalFreshPayoff
import Vegas.Game.PhaseProposalSavedDebt

/-! # Payoff laws from the original selected publication checkpoints -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

omit [Fintype Player] in
private theorem checkpoint_cast_history
    {state other : PhaseRuntimeState (serviceGraph setup mode)} (same : state = other)
    (checkpoint : RecoverySourceCheckpoint setup mode state) :
    (⟨_, (same ▸ checkpoint).trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, checkpoint.trace⟩ := by
  cases same
  rfl

omit [Fintype Player] in
private theorem checkpoint_cast_point
    {state other : PhaseRuntimeState (serviceGraph setup mode)} (same : state = other)
    (checkpoint : RecoverySourceCheckpoint setup mode state) :
    (same ▸ checkpoint).residual.lift
        (ProtocolState.entry (same ▸ checkpoint).residual.tail (same ▸ checkpoint).source) =
      checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source) := by
  cases same
  rfl

omit [Fintype Player] in
private theorem checkpoint_cast_own
    {state other : PhaseRuntimeState (serviceGraph setup mode)} (same : state = other)
    (checkpoint : RecoverySourceCheckpoint setup mode state) (who : Player) :
    (same ▸ checkpoint).source.history who = checkpoint.source.history who := by
  cases same
  rfl

private theorem witness_cast_archive
    {state other : PhaseRuntimeState (serviceGraph setup mode)} (same : state = other)
    (witness : RecoverySourceWitness setup mode plan state)
    (messages : List (Message Player (CommitAttemptPacket (serviceGraph setup mode)))) :
    (same ▸ witness).checkpoint.ArchivedProposals messages ↔
      witness.checkpoint.ArchivedProposals messages := by
  cases same
  rfl

private theorem witness_cast_bindings
    {state other : PhaseRuntimeState (serviceGraph setup mode)} (same : state = other)
    (witness : RecoverySourceWitness setup mode plan state) (who : Player) :
    (same ▸ witness).checkpoint.source.BindingsHoldValues who ↔
      witness.checkpoint.source.BindingsHoldValues who := by
  cases same
  rfl

private theorem witness_cast_history
    {state other : PhaseRuntimeState (serviceGraph setup mode)} (same : state = other)
    (witness : RecoverySourceWitness setup mode plan state) :
    (⟨_, (same ▸ witness).checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, witness.checkpoint.trace⟩ := by
  cases same
  rfl

/-- Genuine saved source debt fixes the actual physical terminal payoff
under every continuation, including arbitrary current response aliases. -/
theorem phaseProposal_checkpoint_debt_finish_payoff
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (players : Player → (app).Policy)
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, some who, execution⟩))
    (debt : PhaseCheckpointDebt setup mode plan who execution.application)
    (response : (app).Action)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    expect ((app).finish initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape) players
        (some ⟨remaining, none, execution.respond app who response⟩))
      (fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who) =
        excludedPayoff who := by
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  let invariant := phaseCheckpointDebt_invariant setup mode runtime leaks plan maximal who
  have responded : PhaseCheckpointDebt setup mode plan who
      (execution.respond app who response).application := invariant.respond execution who response
        debt
  obtain ⟨responseTrace⟩ := (app).raw_trace_respond initial horizon scheduler remaining execution
    who response ((menu).toRawTrace initial horizon scheduler trace)
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind, expect_map]
  rw [expect_congr_on_support (g := fun _ => excludedPayoff who)]
  · exact expect_constant _ _
  intro final reached
  obtain ⟨finalTrace⟩ := (app).raw_trace_runRounds initial horizon scheduler players 0 remaining
    (execution.respond app who response) final (by simpa only [Nat.zero_add] using responseTrace)
      reached
  have finished := (ReservedEpoch.terminal_history_complete runtime leaks tape plan
    (serviceGraph_revealRelaxedOrdered setup mode) maximal (setup.initialLaw.map encodeInputs)
      ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩).1
  exact phaseCheckpointDebt_terminal_payoff setup mode runtime leaks plan maximal
    (setup.initialLaw.map encodeInputs) horizon scheduler players remaining
      (execution.respond app who response) final responseTrace who responded reached finished
        utility excludedPayoff

/-- The SAME selected reveal checkpoint is packaged at its original drained
image, then fed through the existing automatic normalizer and fresh terminal
joint. No endpoint source history or native tape posterior is replaced. -/
theorem phaseProposal_original_publication_payoff_law
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ anchor.execution.application.phases.head?) (kind : phase.kind = .reveal)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some before))
    (endingTrace : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ending))
    (kept : TracePrefix anchorTrace prior)
    (same : before.execution.application.attempt = anchor.execution.application.attempt)
    (idle : ending.actor = none)
    (changed : ending.execution.application.attempt ≠ anchor.execution.application.attempt)
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup mode)).normalize)
    (finished : phase.Finished (phase.drain raw))
    (imageE : (phase.drain raw).excluded = ending.execution.application.current.excluded)
    (selected : RecoverySourceCheckpoint setup mode
      (⟨anchor.execution.application.phases.tail, anchor.execution.application.generation,
        phase.drain raw, phase.drain raw, anchor.execution.application.retired⟩ :
          PhaseRuntimeState (serviceGraph setup mode)))
    (reaches : ∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, witness.checkpoint.trace⟩ ⟨_, selected.trace⟩)
    (publicSteps : Relation.ReflTransGen
      (NativePublicSourceStep (phase.drain raw).native 0 setup.program)
      (witness.checkpoint.residual.lift (ProtocolState.entry witness.checkpoint.residual.tail
        witness.checkpoint.source), anchor.execution.application.entry.excluded)
      (selected.residual.lift (ProtocolState.entry selected.residual.tail selected.source),
        (phase.drain raw).excluded))
    (addresses : ∃ states : List (ProtocolState setup.program × Finset Player),
      ((witness.checkpoint.residual.lift (ProtocolState.entry witness.checkpoint.residual.tail
        witness.checkpoint.source), anchor.execution.application.entry.excluded) :: states).IsChain
          (NativePublicSourceStep (phase.drain raw).native 0 setup.program) ∧
      ((witness.checkpoint.residual.lift (ProtocolState.entry witness.checkpoint.residual.tail
        witness.checkpoint.source), anchor.execution.application.entry.excluded) :: states).getLast
          (List.cons_ne_nil _ _) =
        (selected.residual.lift (ProtocolState.entry selected.residual.tail selected.source),
          (phase.drain raw).excluded) ∧
      setup.recoveryAddressWord selected.trace = setup.recoveryAddressWord
        witness.checkpoint.trace ++
        states.map (fun point => (CommitRecoveryState.atPoint point.1 point.2
          anchor.execution.application.generation).publicAddress))
    (own : ∀ who, who ∉ (phase.drain raw).excluded → selected.source.history who =
      witness.checkpoint.source.history who ++
        (decodeHistory setup.program ((phase.drain raw).native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
            (decodeHistory setup.program
              (anchor.execution.application.entry.native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion mode)) who).length)
    (replay : NativeSourceReplayExtension setup (phase.drain raw).native
      anchor.execution.application.generation witness.checkpoint.trace selected.trace)
    (proper : ∀ who, who ∉ (phase.drain raw).excluded →
      ProtocolState.BindingsHoldValues who setup.program
        (selected.residual.lift (ProtocolState.entry selected.residual.tail selected.source))) :
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy ending.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let q0 := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    ∀ who, (model.runBehavioralTerminalFrom certificate profile ⟨some ending, endingTrace⟩).map
        (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
          final.state who) =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories q0
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
            selected.trace⟩).map (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
  classical
  intro scheduler model certificate profile q0 who
  obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have tail : anchor.execution.application.phases.tail = rest := by rw [phases]; rfl
  obtain ⟨beforeW, beforeArchived, beforeHistory, saved, beforeCheckpoint⟩ :=
    RecoverySourceWitness.prefix_at_same_attempt setup mode runtime leaks bounds plan maximal
      scheduler anchor before anchorTrace prior kept same witness archived
  have controls := phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds
    plan horizon scheduler anchor before anchorTrace prior kept same.symm
  have beforePhases : before.execution.application.phases = phase :: rest := controls.1.trans phases
  have generation : before.execution.application.generation =
      anchor.execution.application.generation := congrArg CommitAttemptId.generation same
  have selectedState :
      (⟨anchor.execution.application.phases.tail, anchor.execution.application.generation,
        phase.drain raw, phase.drain raw, anchor.execution.application.retired⟩ :
        PhaseRuntimeState (serviceGraph setup mode)) =
      ⟨rest, before.execution.application.generation, phase.drain raw, phase.drain raw,
        before.execution.application.retired⟩ := by rw [tail, generation, controls.2.1]
  let chosen : RecoverySourceCheckpoint setup mode
      (⟨rest, before.execution.application.generation, phase.drain raw, phase.drain raw,
        before.execution.application.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)) :=
    selectedState ▸ selected
  have chosenHistory : (⟨_, chosen.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, selected.trace⟩ := checkpoint_cast_history setup mode selectedState selected
  have changedBefore : ending.execution.application.attempt ≠ before.execution.application.attempt
    :=
    fun equal => changed (equal.trans same)
  obtain ⟨rawW, rawCheckpoint, rawHistory⟩ :=
    RecoverySourceWitness.raw_closing_checkpoint setup mode runtime leaks plan before ending
      beforeW raw effect changedBefore
  obtain ⟨fuel, path⟩ := reaches
  have chosenPath : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, rawW.checkpoint.trace⟩ ⟨_, chosen.trace⟩ := by
    rw [rawHistory, beforeHistory, chosenHistory]
    exact path
  have rawSemantic := rawHistory.trans beforeHistory
  have rawPoint : rawW.checkpoint.residual.lift
      (ProtocolState.entry rawW.checkpoint.residual.tail rawW.checkpoint.source) =
      witness.checkpoint.residual.lift
        (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source) := by
    rw [rawCheckpoint, beforeCheckpoint]
    rfl
  have rawOwn (owner : Player) : rawW.checkpoint.source.history owner =
      witness.checkpoint.source.history owner := by
    rw [rawCheckpoint, beforeCheckpoint]
    rfl
  have chosenPoint : chosen.residual.lift
      (ProtocolState.entry chosen.residual.tail chosen.source) =
      selected.residual.lift (ProtocolState.entry selected.residual.tail selected.source) :=
    checkpoint_cast_point setup mode selectedState selected
  have rawAddress := congrArg
    (fun history : setup.commitRecoveryProtocol.History => setup.recoveryAddressWord history.trace)
      rawSemantic
  have chosenAddress := congrArg
    (fun history : setup.commitRecoveryProtocol.History => setup.recoveryAddressWord history.trace)
      chosenHistory
  have selectedMeta := rawW.checkpoint.public_phase_archive plan maximal phase rest beforePhases
    (rawW.suffix.subset (by rw [beforePhases]; exact List.mem_cons_self))
    (by rw [kind]; decide) rawW.aligned rawW.chronology rawW.origins rawW.exclusions
      rawW.failures rawW.archives rawW.receipts rawW.stored rawW.remembered rawW.order
        (by obtain ⟨draw, valid⟩ := rawW.native; exact ⟨draw, phase.drain_invariant raw
          valid.active⟩)
          finished chosen chosenPath (by
      simpa only [rawPoint, chosenPoint, saved] using publicSteps)
    (by simpa only [rawPoint, chosenPoint, saved, rawAddress, chosenAddress, generation]
      using addresses)
    (by
      intro owner survives
      rw [checkpoint_cast_own setup mode selectedState selected owner, rawOwn owner, saved]
      exact own owner survives)
    (by
      change NativeSourceReplayExtension setup (phase.drain raw).native
        before.execution.application.generation rawW.checkpoint.trace chosen.trace
      have readback := (congrArg₂ (fun first last : setup.commitRecoveryProtocol.History =>
        NativeSourceReplayExtension setup (phase.drain raw).native
          anchor.execution.application.generation first.trace last.trace)
            rawSemantic chosenHistory).mpr replay
      exact (congrArg (fun generation : Nat =>
        NativeSourceReplayExtension setup (phase.drain raw).native generation
          rawW.checkpoint.trace chosen.trace) generation).mpr readback)
  obtain ⟨aligned, chronology, origins, delta⟩ := selectedMeta
  let completed := rawW.completed_phase_checkpoint phase rest beforePhases finished chosen
    aligned chronology origins
  have settled : ending.execution.application = PhaseRuntimeState.settle rest
      before.execution.application.generation (phase.drain raw) (phase.drain raw)
        before.execution.application.retired := by
    rw [normalized]
    change PhaseRuntimeState.settle before.execution.application.phases
      before.execution.application.generation before.execution.application.entry raw
        before.execution.application.retired = _
    rw [beforePhases, PhaseRuntimeState.settle_clean phase rest
      before.execution.application.generation before.execution.application.entry raw
        before.execution.application.retired finished (by rw [kind]; simp)]
  obtain ⟨next, nextPath, sourceKernel, _nextDelta, nextArchived⟩ :=
    RecoverySourceWitness.completed_normalized_archived_source setup mode runtime leaks bounds plan
      maximal horizon scheduler before ending prior beforeW beforeArchived raw effect rawW
        rawCheckpoint phase rest beforePhases finished normalized settled completed delta
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories q0
  let finalW : RecoverySourceWitness setup mode plan ending.execution.application := settled.symm
    ▸ next
  have entryE : ending.execution.application.entry.excluded =
      ending.execution.application.current.excluded := by
    rw [settled]
    exact PhaseRuntimeState.settle_entry_excluded_of_same rest
      before.execution.application.generation (phase.drain raw) (phase.drain raw)
        before.execution.application.retired rfl
  have finalArchive : finalW.checkpoint.ArchivedProposals ending.execution.network.inputs :=
    (witness_cast_archive setup mode plan settled.symm next ending.execution.network.inputs).mpr
      nextArchived
  obtain ⟨normalFuel, normalPath⟩ := nextPath
  have preserved := (completed.checkpoint.fresh_normalization_source_law mode rest
    before.execution.application.generation (phase.drain raw) before.execution.application.retired
      completed.order.frontier next.checkpoint normalPath q0
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))).2
  have finalProper : ∀ owner, owner ∉ ending.execution.application.current.excluded →
      finalW.checkpoint.source.BindingsHoldValues owner := by
    intro owner survives
    have survivesImage : owner ∉ (phase.drain raw).excluded := imageE.symm ▸ survives
    have chosenProper : chosen.source.BindingsHoldValues owner := by
      apply (ProtocolState.bindingsHoldValues_entry owner chosen.residual.tail _).mp
      apply (chosen.origin.bindingsHoldValues_lift owner _).mp
      rw [checkpoint_cast_point setup mode selectedState selected]
      exact proper owner survivesImage
    have live : next.checkpoint.source.BindingsHoldValues owner :=
      preserved owner survivesImage chosenProper
    apply (witness_cast_bindings setup mode plan settled.symm next owner).mpr
    intro name payload cell
    exact live cell
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _member, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have fresh : ∀ owner, ∀ record ∈ ending.execution.recall owner,
      record.beforeView.application.2.attempt ≠ ending.execution.application.attempt := by
    rcases effect with ⟨id, message, result, _found, moved, _handled, _rawEq⟩ |
      ⟨command, result, moved, _sampled, _rawEq⟩
    · exact phase_ownRecall_fresh_after_environment runtime leaks initial initialized horizon
        scheduler before ((menu).toRawTrace initial horizon scheduler prior) ending.execution
          (.include id) moved (Ne.symm changedBefore)
    · exact phase_ownRecall_fresh_after_environment runtime leaks initial initialized horizon
        scheduler before ((menu).toRawTrace initial horizon scheduler prior) ending.execution
          (.application command) moved (Ne.symm changedBefore)
  have nativeLaw := phaseProposal_fresh_behavioral_payoff_law setup mode runtime leaks bounds plan
    complete covered maximal values fullValues tape activationGap processingGap gaps margin capacity
      utility excludedPayoff ending idle endingTrace entryE fresh finalW finalArchive finalProper
        who
  rw [nativeLaw]
  have sourceHistory : (⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
        finalW.checkpoint.trace⟩ : setup.proposalRecoveryProtocol.History) =
      ⟨_, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
          next.checkpoint.trace⟩ := by
    exact congrArg (fun history : setup.commitRecoveryProtocol.History =>
      (⟨history.state, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
          history.trace⟩ : setup.proposalRecoveryProtocol.History))
        (witness_cast_history setup mode plan settled.symm next)
  rw [sourceHistory, ← sourceKernel]
  have completedHistory : (⟨_, completed.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, chosen.trace⟩ := rfl
  have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨history.state, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
        history.trace⟩ : setup.proposalRecoveryProtocol.History))
          (completedHistory.trans chosenHistory)
  exact congrArg (fun history : setup.proposalRecoveryProtocol.History =>
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories q0 history).map
        (setup.proposalRecoveryPayoff utility excludedPayoff who)) lifted

end Vegas
