/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPublicPhaseArchive

/-! # Archive metadata at the same selected clean commitment checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The selected clean commitment trace carries its original archive and
chronology metadata before the existing automatic continuation. -/
theorem RecoverySourceCheckpoint.commit_phase_archive
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
    (remembered : state.HistoryCheckpoint) (order : state.PublicFailureOrder)
    (reachable : ∃ inputs, (phase.drain state.current).native.Invariant inputs)
    (finished : phase.Finished (phase.drain state.current))
    (next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)))
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
    PublicChronology.clean_commit checkpoint next plan chronology phase remaining installed
      member kind frontier maximal archiveExclusions savedFailures finished rfl rfl boundary.symm
        rfl rfl path instructions,
    ArchivedSourceOrigins.advance checkpoint next origins phase remaining installed rfl rfl rfl
      boundary aligned saved retained imageStored finished reachable path (fun _ => instructions)
        (fun impossible => False.elim (impossible kind))
        (fun impossible => False.elim (impossible kind))
        (fun _ => checkpoint.chosen_commit_addresses image.native committing ⟨_, next.trace⟩
          path instructions)
        (fun impossible => False.elim (impossible kind)),
    checkpoint.commit_proposal_delta plan next phase remaining installed kind committing
      image.native path instructions⟩

end Vegas
