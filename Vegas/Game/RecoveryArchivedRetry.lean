/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ArchivedSourceRecall
import Vegas.Game.RecoveryCommitCheckpoint

/-! # Chosen retry checkpoints retain the actual archived source action word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source checkpoint's surviving own actions are read from the full physical
archive and its current effective semantic prefix. -/
def RecoverySourceCheckpoint.ArchivedRecall
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) : Prop :=
  ∀ who, who ∉ state.entry.excluded → checkpoint.source.history who =
    decodeHistory setup.program
      ((PhaseRuntimeState.archivedHistory state.retired state.entry.native.config.history).map
        ((toEventGraph setup.program).fromModeCompletion mode)) who

/-- The actual chosen retry checkpoint satisfies archive alignment whenever
its predecessor does. The new archive is the real completed attempt, rather
than a proposed source history or an independently chosen endpoint witness. -/
theorem RecoverySourceCheckpoint.after_commit_retry_archived
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (aligned : checkpoint.ArchivedRecall) (archives : state.ArchivesBefore)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (binding : state.BindingRecord) (receipts : state.ReceiptRecord)
    (remembered : state.HistoryCheckpoint) {inputs} (native : state.Invariant inputs)
    (finished : phase.Finished (phase.drain state.current))
    (missed : (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (survives : (phase.owners \ (phase.drain state.current).excluded).Nonempty) :
    ∃ next : RecoverySourceCheckpoint setup mode state.normalize, next.ArchivedRecall := by
  obtain ⟨next, _point, word⟩ := checkpoint.after_commit_retry committing phase remaining installed
    maximal binding receipts remembered native finished missed survives
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
  refine ⟨next, ?_⟩
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

end Vegas
