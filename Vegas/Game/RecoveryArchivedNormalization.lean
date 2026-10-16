/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedRetry
import Vegas.Game.RecoveryArchivedSourceOrigin
import Vegas.Pending.PhaseSurvivingHistory
import Vegas.Game.RecoveryCommitCheckpoint
import Vegas.Game.RecoverySettledCommitCheckpoint
import Vegas.Game.RecoveryRevealCheckpoint
import Vegas.Game.RecoverySampleCheckpoint
import Vegas.Game.CompiledCommitControl
import Vegas.Pending.PhaseFailureOrderHistory

/-! # Full archived source action words through actual phase normalization -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


private theorem archived_extension
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

/-- The real dispatcher normalization preserves a reachable saved source
checkpoint through unfinished phases, clean advances, retries, exhaustion and
automatic completion of any number of subsequent phases. -/
theorem RecoverySourceCheckpoint.normalized_archived
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    (state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (priorTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      state.entry.excluded state.generation)))
    (aligned : checkpoint.ArchivedRecall)
    (origins : ArchivedSourceOrigins setup mode state.retired ⟨_, priorTrace⟩)
    (archives : state.ArchivesBefore)
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (native : state.Invariant inputs) (binding : state.BindingRecord)
    (receipts : state.ReceiptRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint)
    (order : state.PublicFailureOrder)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) :
    ∃ next : RecoverySourceCheckpoint setup mode state.normalize,
      next.ArchivedRecall ∧
      ∃ (nextTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
          state.normalize.entry.excluded state.normalize.generation))) (fuel : Nat),
        setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, priorTrace⟩ ⟨_, nextTrace⟩ ∧
        ArchivedSourceOrigins setup mode state.normalize.retired ⟨_, nextTrace⟩ := by
  rcases state with ⟨phases, generation, entry, current, retired⟩
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨checkpoint, aligned, priorTrace, 0, .refl 0 _, origins⟩
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
      have nextOffset : phase.low ≤ PhaseRuntimeState.phaseLow remaining :=
        PhaseRuntimeState.phaseLow_suffix frontier.adjacent (List.suffix_cons phase remaining)
      have beforeNext (archive : List (RetiredCommitAttempt
          ((toEventGraph setup.program).withMode mode)))
          (bounded : ∀ record ∈ archive, record.attempt.phase ≤ phase.low)
          (next : RecoveryState ((toEventGraph setup.program).withMode mode)) :
          (⟨remaining, generation, next, next, archive⟩ :
            PhaseRuntimeState ((toEventGraph setup.program).withMode mode)).ArchivesBefore := by
        intro record member
        exact (bounded record member).trans nextOffset
      have oldBefore : ∀ record ∈ retired, record.attempt.phase ≤ phase.low := archives
      have inherited : entry.excluded ⊆ image.excluded := by
        intro who inactive
        exact (imageRecord.excluded who).mpr (Or.inl inactive)
      have retained : entry.native.config.history.IsPrefix image.native.config.history :=
        remembered.trans (phase.drain_history_prefix current)
      have sourcePositive : 0 < eventCount checkpoint.residual.tail := by
        have counted := checkpoint.compiled.countEq
        have nonempty := phase.nonempty
        have bounded := phase.bounded
        change phase.high ≤ eventCount setup.program at bounded
        change phase.low + eventCount checkpoint.residual.tail = eventCount setup.program at counted
        omega
      have imageAgrees : checkpoint.refs.Agrees checkpoint.source.state
          image.native.config.store := by
        intro name cell selected
        exact (checkpoint.refs.get selected).get?_preserved _ _
          (fun field value present => phase.drain_keepsStore current field value
            (stored field value present)) _ (checkpoint.agrees selected)
      have archivedSource {history : setup.commitRecoveryProtocol.History} {fuel : Nat}
          (path : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, priorTrace⟩ history) :
          ArchivedSourceOrigins setup mode
            (retired ++ [⟨⟨phase.low, generation⟩, image.native⟩]) history :=
        ArchivedSourceOrigins.append checkpoint priorTrace origins aligned
          ⟨⟨phase.low, generation⟩, image.native⟩ rfl retained position.1 imageAgrees sourcePositive
          path
      have advance (next : RecoveryState ((toEventGraph setup.program).withMode mode))
          (archive : List (RetiredCommitAttempt ((toEventGraph setup.program).withMode mode)))
          (nextPrefix : next.native.config.cut.IsPrefix phase.high)
          (nextNative : next.native.Invariant inputs)
          (nextBinding : next.native.BindingInvariant)
          (nextReceipts : next.native.ReceiptsComplete)
          (nextCoverage : next.FailureCoverage)
          (nextArchives : (⟨remaining, generation, next, next, archive⟩ :
            PhaseRuntimeState ((toEventGraph setup.program).withMode mode)).ArchivesBefore)
          (nextCheckpoint :
            let nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
              ⟨remaining, generation, next, next, archive⟩
            ∃ checkpoint : RecoverySourceCheckpoint setup mode nextState,
              checkpoint.ArchivedRecall ∧
              ∃ (nextTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
                  (checkpoint.residual.lift
                    (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
                  nextState.entry.excluded nextState.generation))) (fuel : Nat),
                setup.commitRecoveryProtocol.ReachesWithin fuel
                  ⟨_, priorTrace⟩ ⟨_, nextTrace⟩ ∧
                ArchivedSourceOrigins setup mode nextState.retired ⟨_, nextTrace⟩) :
          let finalState := PhaseRuntimeState.settle remaining generation next next archive
          ∃ checkpoint : RecoverySourceCheckpoint setup mode finalState,
            checkpoint.ArchivedRecall ∧
            ∃ (nextTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
                (checkpoint.residual.lift
                  (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
                finalState.entry.excluded finalState.generation))) (fuel : Nat),
              setup.commitRecoveryProtocol.ReachesWithin fuel
                ⟨_, priorTrace⟩ ⟨_, nextTrace⟩ ∧
              ArchivedSourceOrigins setup mode finalState.retired ⟨_, nextTrace⟩ := by
        obtain ⟨nextSource, nextAligned, nextTrace, nextFuel, nextPath, nextOrigins⟩ :=
          nextCheckpoint
        have nextPosition := PhaseRuntimeState.positioned_next phase remaining next
          frontier.adjacent frontier.last nextPrefix
        have nextFrontier : PhaseRuntimeState.Frontier
            (⟨remaining, generation, next, next, archive⟩ :
              PhaseRuntimeState ((toEventGraph setup.program).withMode mode)) :=
          ⟨nextPosition.adjacent, nextPosition.last, nextPosition.positioned⟩
        obtain ⟨result, resultAligned, resultTrace, resultFuel, resultPath, resultOrigins⟩ :=
          ih generation next next archive nextSource nextTrace nextAligned nextOrigins nextArchives
          ⟨nextNative, nextNative⟩
          ⟨nextBinding, nextBinding, fun _ _ => rfl⟩
          (PhaseRuntimeState.fresh_receiptRecord remaining generation next archive nextFrontier
            nextReceipts) (fun _ _ present => present) (⟨[], by simp⟩)
          (PhaseRuntimeState.fresh_publicFailureOrder remaining generation next archive
            nextFrontier nextCoverage) maximal.tail
        exact ⟨result, resultAligned, resultTrace, nextFuel + resultFuel,
          nextPath.trans resultPath, resultOrigins⟩
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
              · obtain ⟨next, nextAligned, nextTrace, fuel, path⟩ :=
                  checkpoint.after_commit_retry_archived priorTrace aligned archives
                    committing phase remaining rfl kind maximal binding receipts remembered native
                    finished missed survives
                refine ⟨next, nextAligned, nextTrace, fuel, path, ?_⟩
                have normalized := PhaseRuntimeState.settle_retry phase remaining generation entry
                  current retired finished kind missed survives
                change ArchivedSourceOrigins setup mode
                  (PhaseRuntimeState.settle (phase :: remaining) generation entry current
                    retired).retired ⟨_, nextTrace⟩
                rw [normalized]
                exact archivedSource path
              · obtain ⟨⟨nextCheckpoint, sourcePrefix, word⟩, normalized⟩ :=
                  checkpoint.after_commit_exhausted priorTrace committing
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
                let archive : List (RetiredCommitAttempt
                    ((toEventGraph setup.program).withMode mode)) :=
                  retired ++ [⟨⟨phase.low, generation⟩, image.native⟩]
                have archiveBefore : ∀ record ∈ archive, record.attempt.phase ≤ phase.low := by
                  intro record member
                  rcases List.mem_append.mp member with old | new
                  · exact oldBefore record old
                  · obtain rfl := List.mem_singleton.mp new
                    exact Nat.le_refl _
                have nextAligned : nextCheckpoint.ArchivedRecall := by
                  intro who active
                  have activeImage : who ∉ image.excluded := by
                    have same : rebuilt.excluded = image.excluded := phase.drain_excluded restored
                    rwa [same] at active
                  have outside : who ∉ phase.owners := fun owned => activeImage (allExcluded owned)
                  have unchanged := phase.ownCompletions_eq_of_unowned entry.native.config
                    image.native.config position.1 within retained who outside
                  have rebuiltUnchanged := phase.drain_ownCompletions restored who activeImage
                  have recovered : PhaseRuntimeState.archivedHistory archive
                      entry.native.config.history = PhaseRuntimeState.archivedHistory retired
                        image.native.config.history :=
                    PhaseRuntimeState.archivedHistory_retry retired
                      ⟨⟨phase.low, generation⟩, image.native⟩ entry.native.config
                        position.1 retained
                  have allOwn :=
                    (PhaseRuntimeState.archivedHistory_own_congr archive
                      rebuilt.native.config.history entry.native.config.history who
                        rebuiltUnchanged).trans
                      ((congrArg (fun past =>
                        ((toEventGraph setup.program).withMode mode).ownCompletions who past)
                          recovered).trans
                          (PhaseRuntimeState.archivedHistory_own_congr retired
                            image.native.config.history entry.native.config.history who unchanged))
                  rw [word who activeImage,
                    aligned who (fun inactive => activeImage (inherited inactive))]
                  exact (decodeHistory_fromMode_congr setup.program mode _ _ who allOwn).symm
                exact advance rebuilt
                  (retired ++ [⟨⟨phase.low, generation⟩, image.native⟩])
                  (phase.finished_prefix rebuilt rebuiltWithin rebuiltFinished) rebuiltNative
                  rebuiltBinding rebuiltRecord.receipts rebuiltCoverage
                  (beforeNext archive archiveBefore rebuilt)
                  (by
                    obtain ⟨nextTrace, nextFuel, nextPath⟩ := sourcePrefix
                    exact ⟨nextCheckpoint, nextAligned, nextTrace, nextFuel, nextPath,
                      archivedSource nextPath⟩)
            · obtain ⟨⟨nextCheckpoint, _sourcePoint, sourcePrefix, word, _intended⟩, normalized⟩ :=
                checkpoint.after_commit_clean priorTrace committing
                phase remaining rfl maximal binding receipts stored remembered native order.coverage
                  finished missed
              rw [normalized]
              exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
                imageCoverage (beforeNext retired oldBefore image)
                ⟨nextCheckpoint, archived_extension checkpoint aligned archives phase remaining rfl
                  image position.1 retained inherited nextCheckpoint word, by
                    obtain ⟨nextTrace, nextFuel, nextPath⟩ := sourcePrefix
                    exact ⟨nextTrace, nextFuel, nextPath, origins.trans nextPath⟩⟩
        | reveal =>
            obtain ⟨nextCheckpoint, sourcePrefix, word, _intended⟩ :=
              checkpoint.after_reveal priorTrace phase remaining rfl kind
              receipts.exclusion stored remembered imageNative.reachable imageOrder finished
            have noRetry : ¬ (phase.kind = .commitment ∧
                ((image.excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
              rintro ⟨impossible, _⟩
              rw [kind] at impossible
              cases impossible
            change
              let finalState :=
                PhaseRuntimeState.settle (phase :: remaining) generation entry current retired
              ∃ checkpoint : RecoverySourceCheckpoint setup mode finalState,
                checkpoint.ArchivedRecall ∧
                ∃ (nextTrace : setup.commitRecoveryProtocol.Trace
                    (some (CommitRecoveryState.atPoint
                      (checkpoint.residual.lift
                        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
                      finalState.entry.excluded finalState.generation))) (fuel : Nat),
                  setup.commitRecoveryProtocol.ReachesWithin fuel
                    ⟨_, priorTrace⟩ ⟨_, nextTrace⟩ ∧
                  ArchivedSourceOrigins setup mode finalState.retired ⟨_, nextTrace⟩
            rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
              finished noRetry]
            exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
              imageCoverage (beforeNext retired oldBefore image)
              ⟨nextCheckpoint, archived_extension checkpoint aligned archives phase remaining rfl
                image position.1 retained inherited nextCheckpoint word, by
                  obtain ⟨nextTrace, nextFuel, nextPath⟩ := sourcePrefix
                  exact ⟨nextTrace, nextFuel, nextPath, origins.trans nextPath⟩⟩
        | sample =>
            obtain ⟨nextCheckpoint, sourcePrefix, word, _intended⟩ :=
              checkpoint.after_sample priorTrace phase remaining rfl kind
              receipts.exclusion stored remembered imageNative.reachable finished
            have noRetry : ¬ (phase.kind = .commitment ∧
                ((image.excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
              rintro ⟨impossible, _⟩
              rw [kind] at impossible
              cases impossible
            change
              let finalState :=
                PhaseRuntimeState.settle (phase :: remaining) generation entry current retired
              ∃ checkpoint : RecoverySourceCheckpoint setup mode finalState,
                checkpoint.ArchivedRecall ∧
                ∃ (nextTrace : setup.commitRecoveryProtocol.Trace
                    (some (CommitRecoveryState.atPoint
                      (checkpoint.residual.lift
                        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
                      finalState.entry.excluded finalState.generation))) (fuel : Nat),
                  setup.commitRecoveryProtocol.ReachesWithin fuel
                    ⟨_, priorTrace⟩ ⟨_, nextTrace⟩ ∧
                  ArchivedSourceOrigins setup mode finalState.retired ⟨_, nextTrace⟩
            rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
              finished noRetry]
            exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
              imageCoverage (beforeNext retired oldBefore image)
              ⟨nextCheckpoint, archived_extension checkpoint aligned archives phase remaining rfl
                image position.1 retained inherited nextCheckpoint word, by
                  obtain ⟨nextTrace, nextFuel, nextPath⟩ := sourcePrefix
                  exact ⟨nextTrace, nextFuel, nextPath, origins.trans nextPath⟩⟩
      · change
          let finalState :=
            PhaseRuntimeState.settle (phase :: remaining) generation entry current retired
          ∃ checkpoint : RecoverySourceCheckpoint setup mode finalState,
            checkpoint.ArchivedRecall ∧
            ∃ (nextTrace : setup.commitRecoveryProtocol.Trace
                (some (CommitRecoveryState.atPoint
                  (checkpoint.residual.lift
                    (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
                  finalState.entry.excluded finalState.generation))) (fuel : Nat),
              setup.commitRecoveryProtocol.ReachesWithin fuel
                ⟨_, priorTrace⟩ ⟨_, nextTrace⟩ ∧
              ArchivedSourceOrigins setup mode finalState.retired ⟨_, nextTrace⟩
        have unfinishedEq : PhaseRuntimeState.settle (phase :: remaining) generation entry
            current retired =
            (⟨phase :: remaining, generation, entry, phase.drain current, retired⟩ :
              PhaseRuntimeState ((toEventGraph setup.program).withMode mode)) := by
          rw [PhaseRuntimeState.settle, ite_eq_right finished]
        rw [unfinishedEq]
        exact ⟨checkpoint.transfer rfl rfl rfl, aligned, priorTrace, 0, .refl 0 _, origins⟩

end Vegas
