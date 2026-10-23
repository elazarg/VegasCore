/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPublicSourceChronology
import Vegas.Game.RecoveryArchivedSourceOrigin
import Vegas.Pending.PhaseFailureOrderHistory
import Vegas.Game.PhaseProposalPhaseDelta

/-! # Archive metadata at the same chosen public-phase checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]


omit [Fintype Player] in
theorem RecoverySourceCheckpoint.public_archive_extension
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (aligned : checkpoint.ArchivedRecall) (archives : state.ArchivesBefore)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining)
    (image : RecoveryState ((toEventGraph setup.program).withMode mode))
    (saved : state.entry.native.config.cut.IsPrefix phase.low)
    (retained : state.entry.native.config.history.IsPrefix image.native.config.history)
    (inherited : state.entry.excluded ⊆ image.excluded)
    (next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, image, image, state.retired⟩ :
        PhaseRuntimeState ((toEventGraph setup.program).withMode mode)))
    (word : ∀ who, who ∉ image.excluded → next.source.history who =
      checkpoint.source.history who ++
        (decodeHistory setup.program (image.native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) who).length) :
    next.ArchivedRecall := by
  intro who active
  rw [word who active, aligned who (fun inactive => active (inherited inactive))]
  symm
  apply decodeArchivedHistory_checkpoint_extension setup.program mode state.retired
    state.entry.native.config image.native.config phase.low _ saved retained who
  intro previous present
  have earlier := archives previous present
  simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
    Option.getD_some] using earlier

/-- The selected public-phase replay carries its exact archive, chronology and
proposal metadata before subsequent automatic normalization. -/
theorem RecoverySourceCheckpoint.public_phase_archive
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (planMaximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (member : phase ∈ plan.phases)
    (noncommit : phase.kind ≠ .commitment)
    (aligned : checkpoint.ArchivedRecall) (chronology : checkpoint.PublicChronology plan)
    (origins : ArchivedSourceOrigins setup mode state.retired ⟨_, checkpoint.trace⟩)
    (archiveExclusions : state.ArchivedExclusions)
    (savedFailures : state.PublicFailureCheckpoint) (archives : state.ArchivesBefore)
    (receipts : state.ReceiptRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint) (order : state.PublicFailureOrder)
    (reachable : ∃ inputs, (phase.drain state.current).native.Invariant inputs)
    (finished : phase.Finished (phase.drain state.current))
    (next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)))
    {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (publicSteps : Relation.ReflTransGen
      (NativePublicSourceStep (phase.drain state.current).native 0 setup.program)
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
        state.entry.excluded)
      (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
        (phase.drain state.current).excluded))
    (publicAddresses : ∃ states : List (ProtocolState setup.program × Finset Player),
      ((checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
        state.entry.excluded) :: states).IsChain
          (NativePublicSourceStep (phase.drain state.current).native 0 setup.program) ∧
      ((checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
        state.entry.excluded) :: states).getLast (List.cons_ne_nil _ _) =
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
          (phase.drain state.current).excluded) ∧
      setup.recoveryAddressWord next.trace = setup.recoveryAddressWord checkpoint.trace ++
        states.map (fun point =>
          (CommitRecoveryState.atPoint point.1 point.2 state.generation).publicAddress))
    (word : ∀ who, who ∉ (phase.drain state.current).excluded →
      next.source.history who = checkpoint.source.history who ++
        (decodeHistory setup.program ((phase.drain state.current).native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) who).length)
    (replay : NativeSourceReplayExtension setup (phase.drain state.current).native
      state.generation checkpoint.trace next.trace) :
    next.ArchivedRecall ∧ next.PublicChronology plan ∧
        ArchivedSourceOrigins setup mode state.retired ⟨_, next.trace⟩ ∧
        checkpoint.ProposalDelta plan next := by
  let image := phase.drain state.current
  have frontier := receipts.exclusion.frontier
  have position := frontier.positioned
  rw [installed] at position
  have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using position.1
  have inherited : state.entry.excluded ⊆ image.excluded := by
    rw [phase.drain_excluded]
    exact order.coverage.inherited
  have retained := remembered.trans (phase.drain_history_prefix state.current)
  have imageStored : KeepsStore state.entry.native image.native :=
    fun field value present => phase.drain_keepsStore state.current field value
      (stored field value present)
  have boundary : phase.high = PhaseRuntimeState.phaseLow remaining := by
    have adjacent := frontier.adjacent
    have ending := frontier.last
    rw [installed] at adjacent ending
    cases remaining with
    | nil => exact ending phase (by simp only [List.getLast?_singleton, Option.mem_some_iff])
    | cons following rest => exact adjacent.rel_head? (y := following) (by simp)
  refine ⟨checkpoint.public_archive_extension aligned archives phase remaining installed image
    position.1 retained inherited next word,
    PublicChronology.advance_public checkpoint next plan chronology phase remaining installed
      member noncommit frontier archiveExclusions savedFailures
        (phase.drain_publicFailureExtension state.current) rfl rfl boundary.symm rfl
          publicAddresses,
    ArchivedSourceOrigins.advance checkpoint next origins phase remaining installed rfl rfl
      rfl boundary aligned saved retained imageStored finished reachable path
        (fun impossible => (noncommit impossible).elim) (fun _ => publicSteps)
        (fun _ => publicAddresses) (fun impossible => (noncommit impossible).elim)
        (fun _ => replay),
    checkpoint.public_proposal_delta plan planMaximal next phase remaining installed member
      noncommit boundary.symm rfl position.1
        (savedFailures.trans (phase.drain_publicFailureExtension state.current)) path replay⟩

end Vegas
