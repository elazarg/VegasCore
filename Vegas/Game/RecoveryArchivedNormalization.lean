/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPublicSourceChronology
import Vegas.Game.RecoveryPublicPhaseArchive
import Vegas.Game.RecoveryArchivedRetry
import Vegas.Game.RecoveryArchivedSourceOrigin
import Vegas.Pending.PhaseSurvivingHistory
import Vegas.Game.RecoveryCommitCheckpoint
import Vegas.Game.RecoverySettledCommitCheckpoint
import Vegas.Game.RecoveryRevealCheckpoint
import Vegas.Game.RecoverySampleHistory
import Vegas.Game.CompiledCommitControl
import Vegas.Pending.PhaseFailureOrderHistory
import Vegas.Game.PhaseProposalPhaseDelta

/-! # Full archived source action words through actual phase normalization -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]


/-- The real dispatcher normalization preserves a reachable saved source
checkpoint through unfinished phases, clean advances, retries, exhaustion and
automatic completion of any number of subsequent phases. -/
theorem RecoverySourceCheckpoint.normalized_archived
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    (state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (suffix : state.phases <:+ plan.phases)
    (chronology : checkpoint.PublicChronology plan)
    (archiveExclusions : state.ArchivedExclusions)
    (savedFailures : state.PublicFailureCheckpoint)
    (aligned : checkpoint.ArchivedRecall)
    (origins : ArchivedSourceOrigins setup mode state.retired ⟨_, checkpoint.trace⟩)
    (archives : state.ArchivesBefore)
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (native : state.Invariant inputs) (binding : state.BindingRecord)
    (receipts : state.ReceiptRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint)
    (order : state.PublicFailureOrder)
    (planMaximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) :
    ∃ next : RecoverySourceCheckpoint setup mode state.normalize,
      next.ArchivedRecall ∧ next.PublicChronology plan ∧
      ∃ fuel : Nat,
        setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩ ∧
        ArchivedSourceOrigins setup mode state.normalize.retired ⟨_, next.trace⟩ ∧
        checkpoint.ProposalDelta plan next := by
  have maximal := (plan.suffix_geometry planMaximal state.phases suffix).2.2
  let priorTrace := checkpoint.trace
  let priorCheckpoint := checkpoint
  rcases state with ⟨phases, generation, entry, current, retired⟩
  induction phases generalizing generation entry current retired with
  | nil =>
      exact ⟨checkpoint, aligned, chronology, 0, .refl 0 _, origins,
        ProposalDelta.of_same_history plan checkpoint checkpoint rfl rfl⟩
  | cons phase remaining ih =>
      let state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
        ⟨phase :: remaining, generation, entry, current, retired⟩
      let image := phase.drain current
      have planMember : phase ∈ plan.phases := suffix.subset (by simp)
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
      have imageArchived := archiveExclusions.active.phase_drain phase
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
      have nextBoundary : phase.high = PhaseRuntimeState.phaseLow remaining := by
        have adjacent := frontier.adjacent
        have ending := frontier.last
        change (phase :: remaining).IsChain _ at adjacent
        change ∀ final ∈ (phase :: remaining).getLast?, _ at ending
        cases remaining with
        | nil =>
            have last := ending phase (by simp only [List.getLast?_singleton,
              Option.mem_some_iff])
            exact last
        | cons next rest =>
            exact adjacent.rel_head? (y := next) (by simp)
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
      have imageStored : KeepsStore entry.native image.native :=
        fun field value present => phase.drain_keepsStore current field value
          (stored field value present)
      have imageAgrees : checkpoint.refs.Agrees checkpoint.source.state
          image.native.config.store := by
        intro name cell selected
        exact (checkpoint.refs.get selected).get?_preserved _ _
          (fun field value present => phase.drain_keepsStore current field value
            (stored field value present)) _ (checkpoint.agrees selected)
      have archivedSource (committing : ProtocolState.atCommit checkpoint.residual.tail
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
          {history : setup.commitRecoveryProtocol.History} {fuel : Nat}
          (path : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, priorTrace⟩ history)
          (instructions : setup.recoveryJointRecall history.trace =
            (checkpoint.commitInstructionWord image.native).reverse ++
              setup.recoveryJointRecall priorTrace) :
          ArchivedSourceOrigins setup mode
            (retired ++ [⟨⟨phase.low, generation⟩, image.native⟩]) history :=
        ArchivedSourceOrigins.append checkpoint origins aligned
          ⟨⟨phase.low, generation⟩, image.native⟩ rfl retained position.1 imageAgrees sourcePositive
          path instructions
          (checkpoint.chosen_commit_addresses image.native committing history path instructions)
      have advance (next : RecoveryState ((toEventGraph setup.program).withMode mode))
          (archive : List (RetiredCommitAttempt ((toEventGraph setup.program).withMode mode)))
          (nextPrefix : next.native.config.cut.IsPrefix phase.high)
          (nextNative : next.native.Invariant inputs)
          (nextBinding : next.native.BindingInvariant)
          (nextReceipts : next.native.ReceiptsComplete)
          (nextCoverage : next.FailureCoverage)
          (nextRecord : SuffixExclusionRecord 0
            (PhaseRuntimeState.archivedFailureOwners archive) next)
          (nextArchives : (⟨remaining, generation, next, next, archive⟩ :
            PhaseRuntimeState ((toEventGraph setup.program).withMode mode)).ArchivesBefore)
          (nextOpening : ∀ (runtime : EventGraphRuntime
              ((toEventGraph setup.program).withMode mode))
            (leaks : Interaction.MessageNetwork.ObservationRule Player
              (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
            (anchor : (phaseApplication runtime leaks).Control),
            PhaseProposal.NormalizationFrame runtime leaks anchor state →
              PhaseProposal.OpeningOrigins anchor.execution.network.inputs next.native)
          (nextCheckpoint :
            let nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
              ⟨remaining, generation, next, next, archive⟩
            ∃ checkpoint : RecoverySourceCheckpoint setup mode nextState,
              checkpoint.ArchivedRecall ∧ checkpoint.PublicChronology plan ∧
              ∃ fuel : Nat,
                setup.commitRecoveryProtocol.ReachesWithin fuel
                  ⟨_, priorTrace⟩ ⟨_, checkpoint.trace⟩ ∧
                ArchivedSourceOrigins setup mode nextState.retired ⟨_, checkpoint.trace⟩ ∧
                priorCheckpoint.ProposalDelta plan checkpoint) :
          let finalState := PhaseRuntimeState.settle remaining generation next next archive
          ∃ checkpoint : RecoverySourceCheckpoint setup mode finalState,
            checkpoint.ArchivedRecall ∧ checkpoint.PublicChronology plan ∧
            ∃ fuel : Nat,
              setup.commitRecoveryProtocol.ReachesWithin fuel
                ⟨_, priorTrace⟩ ⟨_, checkpoint.trace⟩ ∧
              ArchivedSourceOrigins setup mode finalState.retired ⟨_, checkpoint.trace⟩ ∧
              priorCheckpoint.ProposalDelta plan checkpoint := by
        obtain ⟨nextSource, nextAligned, nextChronology, nextFuel, nextPath, nextOrigins,
          nextDelta⟩ :=
          nextCheckpoint
        have nextPosition := PhaseRuntimeState.positioned_next phase remaining next
          frontier.adjacent frontier.last nextPrefix
        have nextFrontier : PhaseRuntimeState.Frontier
            (⟨remaining, generation, next, next, archive⟩ :
              PhaseRuntimeState ((toEventGraph setup.program).withMode mode)) :=
          ⟨nextPosition.adjacent, nextPosition.last, nextPosition.positioned⟩
        obtain ⟨result, resultAligned, resultChronology, resultFuel, resultPath, resultOrigins,
          resultDelta⟩ :=
          ih generation next next archive nextSource
          ((List.suffix_cons phase remaining).trans suffix) nextChronology
          ⟨⟨nextCoverage, nextCoverage, Finset.Subset.refl _⟩, nextRecord, nextRecord⟩
          (State.PublicFailureExtension.refl _) nextAligned nextOrigins nextArchives
          ⟨nextNative, nextNative⟩
          ⟨nextBinding, nextBinding, fun _ _ => rfl⟩
          (PhaseRuntimeState.fresh_receiptRecord remaining generation next archive nextFrontier
            nextReceipts) (fun _ _ present => present) (⟨[], by simp⟩)
          (PhaseRuntimeState.fresh_publicFailureOrder remaining generation next archive
            nextFrontier nextCoverage) maximal.tail
        refine ⟨result, resultAligned, resultChronology, nextFuel + resultFuel,
          nextPath.trans resultPath, resultOrigins, ?_⟩
        apply ProposalDelta.trans plan priorCheckpoint nextSource result nextDelta resultDelta
        · change phase.low ≤ PhaseRuntimeState.phaseLow remaining
          exact nextOffset
        · change PhaseRuntimeState.phaseLow remaining ≤ PhaseRuntimeState.phaseLow
            (PhaseRuntimeState.settle remaining generation next next archive).phases
          exact PhaseRuntimeState.phaseLow_suffix nextFrontier.adjacent
            (PhaseRuntimeState.settle_suffix remaining generation next next archive)
        · intro runtime leaks anchor frame
          apply PhaseProposal.NormalizationFrame.future anchor _
          · have lower := frame.lower
            change anchor.execution.application.attempt.phase ≤ phase.low at lower
            change anchor.execution.application.attempt.phase < PhaseRuntimeState.phaseLow remaining
            have nonempty := phase.nonempty
            omega
          · exact nextOpening runtime leaks anchor frame
          · exact nextOpening runtime leaks anchor frame
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
              · dsimp only [image] at survives
                obtain ⟨next, nextAligned, fuel, path, instructions⟩ :=
                  checkpoint.after_commit_retry_archived aligned archives
                    committing phase remaining rfl kind maximal binding receipts remembered native
                    finished missed survives
                have normalized := PhaseRuntimeState.settle_retry phase remaining generation entry
                  current retired finished kind missed survives
                refine ⟨next, nextAligned, ?_, fuel, path, ?_, ?_⟩
                · apply PublicChronology.failed_commit checkpoint next plan chronology phase
                    remaining rfl planMember kind frontier maximal archiveExclusions
                    savedFailures finished
                  · simp only [PhaseRuntimeState.normalize, normalized]
                  · simp only [PhaseRuntimeState.normalize, normalized, PhaseRuntimeState.restore]
                  · simp only [PhaseRuntimeState.normalize, normalized, survives, ↓reduceIte]
                  · simp only [PhaseRuntimeState.normalize, normalized, survives, ↓reduceIte,
                      PhaseRuntimeState.attempt, List.head?_cons, Option.map_some,
                      Option.getD_some]
                  · exact path
                  · exact instructions
                · change ArchivedSourceOrigins setup mode
                    (PhaseRuntimeState.settle (phase :: remaining) generation entry current
                      retired).retired ⟨_, next.trace⟩
                  rw [normalized]
                  exact archivedSource committing path instructions
                · exact checkpoint.commit_proposal_delta plan next phase remaining rfl kind
                    committing image.native path instructions
              · dsimp only [image] at survives
                obtain ⟨⟨nextCheckpoint, sourcePrefix, word⟩, normalized⟩ :=
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
                have archiveOwners : PhaseRuntimeState.archivedFailureOwners
                    (retired ++ [⟨⟨phase.low, generation⟩, image.native⟩]) = image.excluded := by
                  rw [PhaseRuntimeState.archivedFailureOwners_append]
                  simpa only [PhaseRuntimeState.archivedFailureOwners, List.foldr_cons,
                    List.foldr_nil, Finset.union_empty] using imageArchived.failureOwners_union.symm
                have restoredArchived : SuffixExclusionRecord 0
                    (PhaseRuntimeState.archivedFailureOwners
                      (retired ++ [⟨⟨phase.low, generation⟩, image.native⟩])) restored := by
                  rw [archiveOwners]
                  exact restoredCoverage.suffixRecord
                have rebuiltArchived := restoredArchived.phase_drain phase
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
                  rebuiltBinding rebuiltRecord.receipts rebuiltCoverage rebuiltArchived
                  (beforeNext archive archiveBefore rebuilt)
                  (fun _ _ anchor frame => by
                    have restoredOrigins : PhaseProposal.OpeningOrigins
                        anchor.execution.network.inputs restored.native :=
                      frame.savedOrigins.copy rfl
                    exact restoredOrigins.drain restored.excluded phase)
                  (by
                    obtain ⟨nextFuel, nextPath, instructions⟩ := sourcePrefix
                    refine ⟨nextCheckpoint, nextAligned, ?_, nextFuel, nextPath,
                      archivedSource committing nextPath instructions,
                      checkpoint.commit_proposal_delta plan nextCheckpoint phase remaining rfl kind
                        committing image.native nextPath instructions⟩
                    apply PublicChronology.failed_commit checkpoint nextCheckpoint plan chronology
                      phase remaining rfl planMember kind frontier maximal archiveExclusions
                      savedFailures finished rfl
                    · exact phase.drain_excluded restored
                    · simp only [survives, ↓reduceIte, Nat.add_zero]
                    · simp only [survives, ↓reduceIte]
                      exact nextBoundary.symm
                    · exact nextPath
                    · exact instructions)
            · obtain ⟨⟨nextCheckpoint, _sourcePoint, sourcePrefix, word, _intended⟩, normalized⟩ :=
                checkpoint.after_commit_clean committing
                phase remaining rfl maximal binding receipts stored remembered native order.coverage
                  finished missed
              rw [normalized]
              obtain ⟨nextFuel, nextPath, instructions⟩ := sourcePrefix
              have nextChronology := PublicChronology.clean_commit checkpoint nextCheckpoint plan
                chronology phase remaining rfl planMember kind frontier maximal archiveExclusions
                savedFailures finished rfl rfl nextBoundary.symm rfl rfl nextPath instructions
              exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
                imageCoverage imageArchived (beforeNext retired oldBefore image)
                (fun _ _ _ frame => frame.currentOrigins.drain current.excluded phase)
                ⟨nextCheckpoint, checkpoint.public_archive_extension aligned archives phase
                  remaining rfl
                  image position.1 retained inherited nextCheckpoint word, nextChronology,
                  nextFuel, nextPath, ArchivedSourceOrigins.advance checkpoint
                      nextCheckpoint origins phase remaining rfl rfl rfl rfl
                      nextBoundary aligned position.1 retained imageStored finished
                      ⟨_, imageNative⟩ nextPath (fun _ => instructions)
                      (fun impossible => False.elim (impossible kind))
                      (fun impossible => False.elim (impossible kind))
                      (fun _ => checkpoint.chosen_commit_addresses image.native committing
                        ⟨_, nextCheckpoint.trace⟩ nextPath instructions)
                      (fun impossible => False.elim (impossible kind)),
                  checkpoint.commit_proposal_delta plan nextCheckpoint phase remaining rfl kind
                    committing image.native nextPath instructions⟩
        | reveal =>
            obtain ⟨nextCheckpoint, ⟨nextFuel, nextPath⟩, publicSteps, publicAddresses, word,
              _intended, replay⟩ :=
              checkpoint.after_reveal phase remaining rfl kind
                receipts.exclusion stored remembered imageNative.reachable imageOrder finished
            obtain ⟨nextAligned, nextChronology, nextOrigins, nextDelta⟩ :=
              checkpoint.public_phase_archive plan planMaximal phase remaining rfl planMember
                (by simp only [kind]; decide) aligned chronology origins archiveExclusions
                  savedFailures archives receipts stored remembered order ⟨_, imageNative⟩ finished
                    nextCheckpoint nextPath publicSteps publicAddresses word replay
            have noRetry : ¬ (phase.kind = .commitment ∧
                ((image.excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
              rintro ⟨impossible, _⟩
              rw [kind] at impossible
              cases impossible
            change
              let finalState :=
                PhaseRuntimeState.settle (phase :: remaining) generation entry current retired
              ∃ checkpoint : RecoverySourceCheckpoint setup mode finalState,
                checkpoint.ArchivedRecall ∧ checkpoint.PublicChronology plan ∧
                ∃ fuel : Nat,
                  setup.commitRecoveryProtocol.ReachesWithin fuel
                    ⟨_, priorTrace⟩ ⟨_, checkpoint.trace⟩ ∧
                  ArchivedSourceOrigins setup mode finalState.retired ⟨_, checkpoint.trace⟩ ∧
                  priorCheckpoint.ProposalDelta plan checkpoint
            rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
              finished noRetry]
            exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
              imageCoverage imageArchived (beforeNext retired oldBefore image)
                (fun _ _ _ frame => frame.currentOrigins.drain current.excluded phase)
              ⟨nextCheckpoint, nextAligned, nextChronology, nextFuel, nextPath, nextOrigins,
                nextDelta⟩
        | sample =>
            obtain ⟨nextCheckpoint, ⟨nextFuel, nextPath⟩, publicSteps, publicAddresses, word,
              _intended, replay, _sameExcluded, _sampled⟩ :=
              checkpoint.after_sample_history phase remaining rfl kind
                receipts.exclusion stored remembered imageNative.reachable finished
            obtain ⟨nextAligned, nextChronology, nextOrigins, nextDelta⟩ :=
              checkpoint.public_phase_archive plan planMaximal phase remaining rfl planMember
                (by simp only [kind]; decide) aligned chronology origins archiveExclusions
                  savedFailures archives receipts stored remembered order ⟨_, imageNative⟩ finished
                    nextCheckpoint nextPath publicSteps publicAddresses word replay
            have noRetry : ¬ (phase.kind = .commitment ∧
                ((image.excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
              rintro ⟨impossible, _⟩
              rw [kind] at impossible
              cases impossible
            change
              let finalState :=
                PhaseRuntimeState.settle (phase :: remaining) generation entry current retired
              ∃ checkpoint : RecoverySourceCheckpoint setup mode finalState,
                checkpoint.ArchivedRecall ∧ checkpoint.PublicChronology plan ∧
                ∃ fuel : Nat,
                  setup.commitRecoveryProtocol.ReachesWithin fuel
                    ⟨_, priorTrace⟩ ⟨_, checkpoint.trace⟩ ∧
                  ArchivedSourceOrigins setup mode finalState.retired ⟨_, checkpoint.trace⟩ ∧
                  priorCheckpoint.ProposalDelta plan checkpoint
            rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
              finished noRetry]
            exact advance image retired imagePrefix imageNative imageBinding imageRecord.receipts
              imageCoverage imageArchived (beforeNext retired oldBefore image)
                (fun _ _ _ frame => frame.currentOrigins.drain current.excluded phase)
              ⟨nextCheckpoint, nextAligned, nextChronology, nextFuel, nextPath, nextOrigins,
                nextDelta⟩
      · change
          let finalState :=
            PhaseRuntimeState.settle (phase :: remaining) generation entry current retired
          ∃ checkpoint : RecoverySourceCheckpoint setup mode finalState,
            checkpoint.ArchivedRecall ∧ checkpoint.PublicChronology plan ∧
            ∃ fuel : Nat,
              setup.commitRecoveryProtocol.ReachesWithin fuel
                ⟨_, priorTrace⟩ ⟨_, checkpoint.trace⟩ ∧
              ArchivedSourceOrigins setup mode finalState.retired ⟨_, checkpoint.trace⟩ ∧
                  priorCheckpoint.ProposalDelta plan checkpoint
        have unfinishedEq : PhaseRuntimeState.settle (phase :: remaining) generation entry
            current retired =
            (⟨phase :: remaining, generation, entry, phase.drain current, retired⟩ :
              PhaseRuntimeState ((toEventGraph setup.program).withMode mode)) := by
          rw [PhaseRuntimeState.settle, ite_eq_right finished]
        rw [unfinishedEq]
        refine ⟨checkpoint.transfer rfl rfl rfl, aligned, ?_, 0, .refl 0 _, origins,
          ProposalDelta.of_same_history plan checkpoint _ rfl rfl⟩
        apply PublicChronology.current checkpoint plan chronology image
          (phase.drain_publicFailureExtension current)
        intro event completed
        exact position.2.1 event completed

end Vegas
