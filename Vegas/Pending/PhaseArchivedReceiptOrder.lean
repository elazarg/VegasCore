/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseArchivedExclusionEntries
import Vegas.Pending.PhaseAcceptedOrder
import Vegas.Pending.PhaseRetiredCompletion

/-! # Actual source order of accepted receipts in every retired attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Every archived receipt respects the source order and the saved exclusion
set reconstructed from precisely its preceding archives. -/
def RetiredReceiptOrderFrom (inherited : Finset Player) :
    List (RetiredCommitAttempt graph) → Prop
  | [] => True
  | record :: rest =>
    BindingReceiptOrder record.attempt.phase
        (inherited ∪ record.state.failureOwnersBefore record.attempt.phase) record.state.accepted ∧
      RetiredReceiptOrderFrom (inherited ∪ record.state.failureOwners) rest

theorem retiredReceiptOrderFrom_append (inherited : Finset Player)
    (first second : List (RetiredCommitAttempt graph)) :
    RetiredReceiptOrderFrom inherited (first ++ second) ↔
      RetiredReceiptOrderFrom inherited first ∧
        RetiredReceiptOrderFrom (inherited ∪ archivedFailureOwners first) second := by
  induction first generalizing inherited with
  | nil => simp only [List.nil_append, RetiredReceiptOrderFrom, archivedFailureOwners,
      List.foldr_nil, Finset.union_empty, true_and]
  | cons record rest ih =>
    simp only [List.cons_append, RetiredReceiptOrderFrom, ih, archivedFailureOwners,
      List.foldr_cons, Finset.union_assoc, and_assoc]

/-- Each index uses its actual chronological entry-exclusion readout. -/
theorem RetiredReceiptOrderFrom.getElem {inherited : Finset Player}
    {retired : List (RetiredCommitAttempt graph)}
    (valid : RetiredReceiptOrderFrom inherited retired)
    (index : Nat) (bound : index < retired.length) :
    BindingReceiptOrder retired[index].attempt.phase
      ((archivedExclusionEntriesFrom inherited retired)[index]'(by
        rw [archivedExclusionEntriesFrom_length]; exact bound)).2
      retired[index].state.accepted := by
  induction retired generalizing inherited index with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at bound
  | cons record rest ih =>
    cases index with
    | zero => exact valid.1
    | succ index => exact ih valid.2 index (Nat.lt_of_succ_lt_succ bound)

/-- Native provenance needed while retaining receipt order across rollback. -/
structure ArchivedReceiptRecord (state : PhaseRuntimeState graph) : Prop where
  receipts : state.ReceiptRecord
  exclusions : state.ArchivedExclusions
  checkpoint : state.PublicFailureCheckpoint
  retired : RetiredReceiptOrderFrom ∅ state.retired

/-- Closing and archiving a commitment keeps its existing source-ordered
receipts under that attempt's own saved exclusions. Automatic rebuilt attempts
use their new saved exclusions without changing the older archived condition. -/
theorem settle_archivedReceiptRecord (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (valid : ArchivedReceiptRecord
      (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph)) :
    (settle phases generation entry current retired).ArchivedReceiptRecord := by
  refine ⟨settle_receiptRecord _ _ _ _ _ valid.receipts,
    settle_archivedExclusions _ _ _ _ _ valid.exclusions,
    settle_publicFailureCheckpoint _ _ _ _ _ valid.checkpoint, ?_⟩
  induction phases generalizing generation entry current retired with
  | nil => exact valid.retired
  | cons phase remaining ih =>
    obtain ⟨adjacent, last, saved, within⟩ := valid.receipts.exclusion.frontier
    have member : phase ∈ (phase :: remaining).head? := by simp
    have drained := valid.exclusions.active.phase_drain phase
    have drainedWithin := phase.drain_within current within
    have drainedCoverage := valid.exclusions.coverage.active.drain phase
    have inheritedDrained : entry.excluded ⊆ (phase.drain current).excluded := by
      rw [phase.drain_excluded]
      exact valid.exclusions.coverage.inherited
    have restoredCoverage := restore_failureCoverage entry (phase.drain current)
      valid.exclusions.coverage.saved inheritedDrained
    have rebuiltCoverage := restoredCoverage.drain phase
    have archiveEq : archivedFailureOwners
        (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) =
          (phase.drain current).excluded := by
      rw [archivedFailureOwners_append]
      simpa only [archivedFailureOwners, List.foldr_cons, List.foldr_nil,
        Finset.union_empty] using drained.failureOwners_union.symm
    have restored : SuffixExclusionRecord 0
        (archivedFailureOwners
          (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]))
        (restore entry (phase.drain current)) := by
      rw [archiveEq]
      exact restoredCoverage.suffixRecord
    have rebuilt := restored.phase_drain phase
    have restoredWithin : (restore entry (phase.drain current)).native.config.cut.Within
        phase.low phase.high := saved.within phase.nonempty.le
    have rebuiltWithin := phase.drain_within (restore entry (phase.drain current)) restoredWithin
    simp only [settle]
    split
    · rename_i finished
      split
      · rename_i failure
        have archived : RetiredReceiptOrderFrom ∅
            (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) := by
          apply (retiredReceiptOrderFrom_append _ _ _).mpr
          refine ⟨valid.retired, ?_, trivial⟩
          have failures := State.PublicFailureExtension.failureOwnersBefore_eq
            (valid.checkpoint.trans (phase.drain_publicFailureExtension current)) phase.low saved
          have ordered := (valid.receipts.ordered phase member failure.1).congr
            (phase.drain_tables current).1
          simpa only [RetiredReceiptOrderFrom, Finset.empty_union, failures,
            ← valid.exclusions.saved_eq] using ordered
        split
        · exact archived
        · rename_i exhausted
          have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
            intro owner owned
            by_contra outside
            exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨owned, outside⟩⟩
          have completed := phase.drain_finished_of_excluded
            (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
          have next := positioned_next phase remaining _ adjacent last
            (phase.finished_prefix _ rebuiltWithin completed)
          exact ih _ _ _ _ ⟨fresh_receiptRecord _ _ _ _
              ⟨next.adjacent, next.last, next.positioned⟩ rebuilt.receipts,
            ⟨⟨rebuiltCoverage, rebuiltCoverage, Finset.Subset.refl _⟩, rebuilt, rebuilt⟩,
            State.PublicFailureExtension.refl _, archived⟩
      · have next := positioned_next phase remaining _ adjacent last
          (phase.finished_prefix _ drainedWithin finished)
        exact ih _ _ _ _ ⟨fresh_receiptRecord _ _ _ _
            ⟨next.adjacent, next.last, next.positioned⟩ drained.receipts,
          ⟨⟨drainedCoverage, drainedCoverage, Finset.Subset.refl _⟩, drained, drained⟩,
          State.PublicFailureExtension.refl _, valid.retired⟩
    · exact valid.retired

theorem initial_archivedReceiptRecord (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).ArchivedReceiptRecord := by
  refine ⟨initial_receiptRecord plan inputs, initial_archivedExclusions plan inputs,
    initial_publicFailureCheckpoint plan inputs, ?_⟩
  have empty := (settle_generation_archive_of_same_excluded plan.phases 0
    (⟨State.initial inputs, ∅⟩ : RecoveryState graph) ⟨State.initial inputs, ∅⟩ [] rfl).2
  change RetiredReceiptOrderFrom ∅ (initial plan inputs).retired
  change (initial plan inputs).retired = [] at empty
  rw [empty]
  trivial

end PhaseRuntimeState

/-- Every actual raw dispatcher operation preserves the chronological archived
receipt certificate as well as the live certificate needed to create it. -/
theorem phaseApplication_archivedReceiptRecord (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (ordered : graph.RevealRelaxedOrdered) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.ArchivedReceiptRecord where
  submit state who material valid :=
    ⟨(phaseApplication_receiptRecord runtime leaks ordered).submit _ _ _ valid.receipts,
      (phaseApplication_archivedExclusions runtime leaks).submit _ _ _ valid.exclusions,
      (phaseApplication_publicFailureCheckpoint runtime leaks).submit _ _ _ valid.checkpoint,
      valid.retired⟩
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      have notExcluded : state.current.excludedCall message.payload.packet.call = false := by
        cases value : state.current.excludedCall message.payload.packet.call with
        | false => rfl
        | true =>
          simp only [value, Bool.not_true, Bool.and_false, Bool.false_eq_true] at allowed
      apply PhaseRuntimeState.settle_archivedReceiptRecord
      refine ⟨valid.receipts.inclusionResult runtime state _ native authorized notExcluded
          handled ordered, ?_, ?_, valid.retired⟩
      · exact ⟨⟨valid.exclusions.coverage.saved,
            valid.exclusions.coverage.active.inclusionResult runtime _ native handled,
            valid.exclusions.coverage.inherited.trans
              (state.current.inclusionResult_excluded_subset _ _)⟩,
          valid.exclusions.saved, valid.exclusions.active.inclusionResult runtime _ native handled⟩
      · exact valid.checkpoint.trans
          (completionStep_handle runtime _ native _ handled).publicFailureExtension
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_archivedReceiptRecord
      refine ⟨valid.receipts.environmentResult runtime state command native allowed supported,
        ?_, ?_, valid.retired⟩
      · exact ⟨⟨valid.exclusions.coverage.saved,
            valid.exclusions.coverage.active.environmentResult runtime command native supported,
            valid.exclusions.coverage.inherited.trans
              (state.current.environmentResult_excluded_subset _ _)⟩,
          valid.exclusions.saved,
          valid.exclusions.active.environmentResult runtime command native supported⟩
      · exact valid.checkpoint.trans
          (completionStep_environmentStep runtime _ native command supported).publicFailureExtension
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Genuine initialized raw histories retain the actual source receipt order
of every retired attempt under its own historical entry exclusions. -/
theorem phaseArchivedReceiptRecord_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.ArchivedReceiptRecord :=
  (phaseApplication_archivedReceiptRecord runtime leaks ordered).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_archivedReceiptRecord plan draw) trace

end Vegas.EventGraphRuntime
