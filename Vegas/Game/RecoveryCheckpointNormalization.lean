/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitCheckpoint
import Vegas.Game.RecoverySettledCommitCheckpoint
import Vegas.Game.RecoveryRevealCheckpoint
import Vegas.Game.RecoverySampleCheckpoint
import Vegas.Game.CompiledCommitControl
import Vegas.Pending.PhaseFailureOrderHistory

/-! # Source checkpoints through actual automatic phase normalization -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The real dispatcher normalization preserves a reachable saved source
checkpoint through unfinished phases, clean advances, retries, exhaustion and
automatic completion of any number of subsequent phases. -/
theorem RecoverySourceCheckpoint.normalized
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    (state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (native : state.Invariant inputs) (binding : state.BindingRecord)
    (receipts : state.ReceiptRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint)
    (order : state.PublicFailureOrder)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) :
    Nonempty (RecoverySourceCheckpoint setup mode state.normalize) := by
  rcases state with ⟨phases, generation, entry, current, retired⟩
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨checkpoint⟩
  | cons phase remaining ih =>
      let state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
        ⟨phase :: remaining, generation, entry, current, retired⟩
      let image := phase.drain current
      have member : phase ∈ state.phases.head? := by
        exact Option.mem_some_iff.mpr rfl
      have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
        (toEventGraph_barrierOrdered setup.program) mode
      have frontier := receipts.exclusion.frontier
      have position := frontier.positioned
      have within := phase.drain_within current position.2
      have imageRecord := (receipts.exclusion.installed phase member).phase_drain phase
      have imageNative := phase.drain_invariant current native.active
      have imageBinding := phase.drain_bindingInvariant current binding.active
      have imageCoverage := order.coverage.active.drain phase
      have imageOrder := phase.orderedPublicFailures_drain phase.low entry.excluded current
        (order.publicationOrder phase member) order.coverage.active order.coverage.inherited
        graphOrder
      have advance (next : RecoveryState ((toEventGraph setup.program).withMode mode))
          (archive : List (RetiredCommitAttempt ((toEventGraph setup.program).withMode mode)))
          (nextPrefix : next.native.config.cut.IsPrefix phase.high)
          (nextNative : next.native.Invariant inputs)
          (nextBinding : next.native.BindingInvariant)
          (nextReceipts : next.native.ReceiptsComplete)
          (nextCoverage : next.FailureCoverage)
          (nextCheckpoint : Nonempty (RecoverySourceCheckpoint setup mode
            (⟨remaining, generation, next, next, archive⟩ :
              PhaseRuntimeState ((toEventGraph setup.program).withMode mode)))) :
          Nonempty (RecoverySourceCheckpoint setup mode
            (PhaseRuntimeState.settle remaining generation next next archive)) := by
        obtain ⟨nextSource⟩ := nextCheckpoint
        have nextPosition := PhaseRuntimeState.positioned_next phase remaining next
          frontier.adjacent frontier.last nextPrefix
        have nextFrontier : PhaseRuntimeState.Frontier
            (⟨remaining, generation, next, next, archive⟩ :
              PhaseRuntimeState ((toEventGraph setup.program).withMode mode)) :=
          ⟨nextPosition.adjacent, nextPosition.last, nextPosition.positioned⟩
        exact ih generation next next archive nextSource ⟨nextNative, nextNative⟩
          ⟨nextBinding, nextBinding, fun _ _ => rfl⟩
          (PhaseRuntimeState.fresh_receiptRecord remaining generation next archive nextFrontier
            nextReceipts) (fun _ _ present => present) (⟨[], by simp⟩)
          (PhaseRuntimeState.fresh_publicFailureOrder remaining generation next archive
            nextFrontier nextCoverage) maximal.tail
      by_cases finished : phase.Finished (phase.drain current)
      · have imagePrefix := phase.finished_prefix image within finished
        cases kind : phase.kind with
        | commitment =>
            have committing := checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
              checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations
              checkpoint.registry checkpoint.embedding checkpoint.before state.attempt.phase
              phase kind rfl checkpoint.source
            by_cases missed : ((image.excluded \ entry.excluded) ∩ phase.owners).Nonempty
            · by_cases survives : (phase.owners \ image.excluded).Nonempty
              · obtain ⟨nextCheckpoint, _recall⟩ := checkpoint.after_commit_retry committing
                  phase remaining rfl maximal binding receipts remembered native finished
                  missed survives
                exact ⟨nextCheckpoint⟩
              · obtain ⟨⟨nextCheckpoint, _recall⟩, normalized⟩ :=
                  checkpoint.after_commit_exhausted committing
                  phase remaining rfl maximal binding receipts stored finished missed survives
                rw [normalized]
                let restored := PhaseRuntimeState.restore entry image
                let rebuilt := phase.drain restored
                have inherited : entry.excluded ⊆ image.excluded := by
                  rw [phase.drain_excluded]
                  exact order.coverage.inherited
                have restoredNative := PhaseRuntimeState.restore_invariant entry image native.saved
                have rebuiltNative := phase.drain_invariant restored restoredNative
                have fixed : KeepsFixedCandidates entry.native image.native := by
                  intro candidate known
                  rw [(phase.drain_tables current).2.1]
                  exact binding.fixed candidate known
                have restoredBinding := PhaseRuntimeState.restore_bindingInvariant entry image
                  binding.saved fixed
                have rebuiltBinding := phase.drain_bindingInvariant restored restoredBinding
                have restoredReceipts : restored.native.ReceiptsComplete := by
                  intro event candidate accepted
                  exact receipts.exclusion.saved event candidate accepted
                have restoredRecord := SuffixExclusionRecord.of_prefix restoredReceipts position.1
                  rfl
                have rebuiltRecord := restoredRecord.phase_drain phase
                have restoredCoverage := PhaseRuntimeState.restore_failureCoverage entry image
                  order.coverage.saved inherited
                have rebuiltCoverage := restoredCoverage.drain phase
                have allExcluded : phase.owners ⊆ restored.excluded := by
                  intro owner owned
                  by_contra active
                  exact survives ⟨owner, Finset.mem_sdiff.mpr ⟨owned, active⟩⟩
                have rebuiltWithin := phase.drain_within restored (position.1.within
                  phase.nonempty.le)
                have rebuiltFinished := phase.drain_finished_of_excluded restored
                  (position.1.within phase.nonempty.le) kind allExcluded
                exact advance rebuilt
                  (retired ++ [⟨⟨phase.low, generation⟩, image.native⟩])
                  (phase.finished_prefix rebuilt rebuiltWithin rebuiltFinished) rebuiltNative
                  rebuiltBinding rebuiltRecord.receipts rebuiltCoverage ⟨nextCheckpoint⟩
            · obtain ⟨⟨nextCheckpoint, _sourcePoint, _recall, _intended⟩, normalized⟩ :=
                checkpoint.after_commit_clean committing
                phase remaining rfl maximal binding receipts stored remembered native order.coverage
                  finished missed
              rw [normalized]
              exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
                imageCoverage ⟨nextCheckpoint⟩
        | reveal =>
            obtain ⟨nextCheckpoint, _history, _intended⟩ :=
              checkpoint.after_reveal phase remaining rfl kind
              receipts.exclusion stored remembered imageNative.reachable imageOrder finished
            have noRetry : ¬ (phase.kind = .commitment ∧
                ((image.excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
              rintro ⟨impossible, _⟩
              rw [kind] at impossible
              cases impossible
            change Nonempty (RecoverySourceCheckpoint setup mode
              (PhaseRuntimeState.settle (phase :: remaining) generation entry current retired))
            rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
              finished noRetry]
            exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
              imageCoverage ⟨nextCheckpoint⟩
        | sample =>
            obtain ⟨nextCheckpoint, _history, _intended⟩ :=
              checkpoint.after_sample phase remaining rfl kind
              receipts.exclusion stored remembered imageNative.reachable finished
            have noRetry : ¬ (phase.kind = .commitment ∧
                ((image.excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
              rintro ⟨impossible, _⟩
              rw [kind] at impossible
              cases impossible
            change Nonempty (RecoverySourceCheckpoint setup mode
              (PhaseRuntimeState.settle (phase :: remaining) generation entry current retired))
            rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
              finished noRetry]
            exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
              imageCoverage ⟨nextCheckpoint⟩
      · change Nonempty (RecoverySourceCheckpoint setup mode
          (PhaseRuntimeState.settle (phase :: remaining) generation entry current retired))
        simp only [PhaseRuntimeState.settle, finished, ↓reduceIte]
        exact ⟨checkpoint.transfer rfl rfl rfl⟩

end Vegas
