/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPublicPhaseArchive

/-! # Full archive metadata at the same surviving retry checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- The surviving action word of the selected retry identifies its full
archived own history. The checkpoint and word are the actual producer outputs. -/
theorem RecoverySourceCheckpoint.retry_archive_extension
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (aligned : checkpoint.ArchivedRecall) (archives : state.ArchivesBefore)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (receipts : state.ReceiptRecord) (remembered : state.HistoryCheckpoint)
    (finished : phase.Finished (phase.drain state.current))
    (missed : (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (survives : (phase.owners \ (phase.drain state.current).excluded).Nonempty)
    (next : RecoverySourceCheckpoint setup mode state.normalize)
    (word : ∀ who, who ∉ (phase.drain state.current).excluded →
      next.source.history who = checkpoint.source.history who ++
        (decodeHistory setup.program ((phase.drain state.current).native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) who).length) :
    next.ArchivedRecall := by
  have positioned := receipts.exclusion.frontier.positioned
  rw [installed] at positioned
  have member : phase ∈ state.phases.head? := by
    rw [installed]
    exact Option.mem_some_iff.mpr rfl
  have record := (receipts.exclusion.installed phase member).phase_drain phase
  have offset : state.attempt.phase = phase.low := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  have normalized : state.normalize =
      ⟨phase :: remaining, state.generation + 1,
        PhaseRuntimeState.restore state.entry (phase.drain state.current),
        phase.drain (PhaseRuntimeState.restore state.entry (phase.drain state.current)),
        state.retired ++
          [⟨⟨phase.low, state.generation⟩, (phase.drain state.current).native⟩]⟩ := by
    unfold PhaseRuntimeState.normalize
    rw [installed]
    exact PhaseRuntimeState.settle_retry phase remaining state.generation state.entry
      state.current state.retired finished kind missed survives
  have archived : PhaseRuntimeState.archivedHistory state.normalize.retired
      state.normalize.entry.native.config.history = PhaseRuntimeState.archivedHistory state.retired
        (phase.drain state.current).native.config.history := by
    unfold PhaseRuntimeState.normalize
    rw [installed]
    exact PhaseRuntimeState.settle_retry_archivedHistory phase remaining state.generation
      state.entry state.current state.retired positioned.1 remembered finished kind missed survives
  intro who active
  have activeImage : who ∉ (phase.drain state.current).excluded := by
    simpa only [normalized, PhaseRuntimeState.restore] using active
  have activeEntry : who ∉ state.entry.excluded := by
    intro inactive
    exact activeImage ((record.excluded who).mpr (Or.inl inactive))
  rw [word who activeImage, aligned who activeEntry, archived]
  symm
  exact decodeArchivedHistory_checkpoint_extension setup.program mode state.retired
    state.entry.native.config (phase.drain state.current).native.config phase.low
    (fun previous present => (archives previous present).trans_eq offset) positioned.1
    (remembered.trans (phase.drain_history_prefix state.current)) who


/-- The actual failed-attempt path supplies chronology, archive origins and
the proposal increment at its selected retry checkpoint. -/
theorem RecoverySourceCheckpoint.retry_phase_archive
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (member : phase ∈ plan.phases)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (kind : phase.kind = .commitment)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (aligned : checkpoint.ArchivedRecall) (chronology : checkpoint.PublicChronology plan)
    (origins : ArchivedSourceOrigins setup mode state.retired ⟨_, checkpoint.trace⟩)
    (archiveExclusions : state.ArchivedExclusions)
    (savedFailures : state.PublicFailureCheckpoint) (archives : state.ArchivesBefore)
    (receipts : state.ReceiptRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint)
    (finished : phase.Finished (phase.drain state.current))
    (missed : (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (survives : (phase.owners \ (phase.drain state.current).excluded).Nonempty)
    (next : RecoverySourceCheckpoint setup mode state.normalize)
    {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (instructions : setup.recoveryJointRecall next.trace =
      (checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (word : ∀ who, who ∉ (phase.drain state.current).excluded →
      next.source.history who = checkpoint.source.history who ++
        (decodeHistory setup.program ((phase.drain state.current).native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) who).length) :
    next.ArchivedRecall ∧ next.PublicChronology plan ∧
      ArchivedSourceOrigins setup mode state.normalize.retired ⟨_, next.trace⟩ ∧
      checkpoint.ProposalDelta plan next := by
  let image := phase.drain state.current
  have frontier := receipts.exclusion.frontier
  have position := frontier.positioned
  rw [installed] at position
  have normalized : state.normalize =
      ⟨phase :: remaining, state.generation + 1,
        PhaseRuntimeState.restore state.entry image,
        phase.drain (PhaseRuntimeState.restore state.entry image),
        state.retired ++ [⟨⟨phase.low, state.generation⟩, image.native⟩]⟩ := by
    unfold PhaseRuntimeState.normalize
    rw [installed]
    exact PhaseRuntimeState.settle_retry phase remaining state.generation state.entry
      state.current state.retired finished kind missed survives
  have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using position.1
  have retained := remembered.trans (phase.drain_history_prefix state.current)
  have imageAgrees : checkpoint.refs.Agrees checkpoint.source.state
      image.native.config.store := by
    intro name cell selected
    exact (checkpoint.refs.get selected).get?_preserved _ _
      (fun field value present => phase.drain_keepsStore state.current field value
        (stored field value present)) _ (checkpoint.agrees selected)
  have positive : 0 < eventCount checkpoint.residual.tail := by
    have counted := checkpoint.compiled.countEq
    have nonempty := phase.nonempty
    have bounded := phase.bounded
    change phase.high ≤ eventCount setup.program at bounded
    change state.attempt.phase + eventCount checkpoint.residual.tail =
      eventCount setup.program at counted
    have low : state.attempt.phase = phase.low := by
      simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
        Option.getD_some]
    omega
  refine ⟨checkpoint.retry_archive_extension aligned archives phase remaining installed kind
    receipts remembered finished missed survives next word, ?_, ?_,
    checkpoint.commit_proposal_delta plan next phase remaining installed kind committing
      image.native path instructions⟩
  · apply PublicChronology.failed_commit checkpoint next plan chronology phase remaining
      installed member kind frontier maximal archiveExclusions savedFailures finished
    · simp only [normalized, image]
    · simp only [normalized, PhaseRuntimeState.restore, image]
    · simp only [normalized, survives, ↓reduceIte, image]
    · simp only [normalized, survives, ↓reduceIte, PhaseRuntimeState.attempt, image,
        List.head?_cons, Option.map_some, Option.getD_some]
    · exact path
    · exact instructions
  · have retiredEq := congrArg PhaseRuntimeState.retired normalized
    rw [retiredEq]
    exact ArchivedSourceOrigins.append checkpoint origins aligned
      ⟨⟨phase.low, state.generation⟩, image.native⟩
      (by simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
        Option.getD_some])
      retained saved imageAgrees positive path instructions
      (checkpoint.chosen_commit_addresses image.native committing ⟨_, next.trace⟩ path
        instructions)

end Vegas
