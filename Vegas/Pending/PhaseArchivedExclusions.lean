/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.ExclusionFailureOwners

/-! # Public failure witnesses for saved exclusions across rollback -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The inherited set and the surviving native failure witnesses jointly
determine every permanent exclusion in an exact suffix record. -/
theorem SuffixExclusionRecord.failureOwners_union {inherited : Finset Player}
    {state : RecoveryState graph} (record : SuffixExclusionRecord 0 inherited state) :
    state.excluded = inherited ∪ state.native.failureOwners := by
  classical
  ext owner
  simp only [Finset.mem_union, State.failureOwners, Finset.mem_filter, Finset.mem_univ,
    true_and]
  simpa only [Nat.zero_le, true_and] using record.excluded owner

namespace PhaseRuntimeState

/-- Public failure owners in the permanently retained attempt records. -/
def archivedFailureOwners (retired : List (RetiredCommitAttempt graph)) : Finset Player :=
  retired.foldr (fun record owners => record.state.failureOwners ∪ owners) ∅

theorem archivedFailureOwners_append (first second : List (RetiredCommitAttempt graph)) :
    archivedFailureOwners (first ++ second) =
      archivedFailureOwners first ∪ archivedFailureOwners second := by
  induction first with
  | nil => simp only [List.nil_append, archivedFailureOwners, List.foldr_nil, Finset.empty_union]
  | cons record rest ih =>
    simpa only [List.cons_append, archivedFailureOwners, List.foldr_cons,
      Finset.union_assoc] using congrArg (record.state.failureOwners ∪ ·) ih

/-- Saved and current exclusions have actual witnesses either in a retired
attempt or in the corresponding surviving native state. -/
structure ArchivedExclusions (state : PhaseRuntimeState graph) : Prop where
  coverage : state.FailureCoverage
  saved : SuffixExclusionRecord 0 (archivedFailureOwners state.retired) state.entry
  active : SuffixExclusionRecord 0 (archivedFailureOwners state.retired) state.current

/-- Normalization records a failed attempt before rollback, so no permanent
exclusion loses its public failure witness when the live state is restored. -/
theorem settle_archivedExclusions (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (valid : ArchivedExclusions
      (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph)) :
    (settle phases generation entry current retired).ArchivedExclusions := by
  induction phases generalizing generation entry current retired with
  | nil => exact valid
  | cons phase remaining ih =>
    have drained := valid.active.phase_drain phase
    have drainedCoverage := valid.coverage.active.drain phase
    have inheritedDrained : entry.excluded ⊆ (phase.drain current).excluded := by
      rw [phase.drain_excluded]
      exact valid.coverage.inherited
    have restoredCoverage := restore_failureCoverage entry (phase.drain current)
      valid.coverage.saved inheritedDrained
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
    have rebuiltInherited : (restore entry (phase.drain current)).excluded ⊆
        (phase.drain (restore entry (phase.drain current))).excluded := by
      rw [phase.drain_excluded]
    simp only [settle]
    split
    · split
      · split
        · exact ⟨⟨restoredCoverage, rebuiltCoverage, rebuiltInherited⟩, restored, rebuilt⟩
        · exact ih _ _ _ _ ⟨⟨rebuiltCoverage, rebuiltCoverage, Finset.Subset.refl _⟩,
            rebuilt, rebuilt⟩
      · exact ih _ _ _ _ ⟨⟨drainedCoverage, drainedCoverage, Finset.Subset.refl _⟩,
          drained, drained⟩
    · exact ⟨⟨valid.coverage.saved, drainedCoverage, inheritedDrained⟩, valid.saved, drained⟩

theorem initial_archivedExclusions (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).ArchivedExclusions := by
  apply settle_archivedExclusions
  have record : SuffixExclusionRecord 0 ∅
      (⟨State.initial inputs, ∅⟩ : RecoveryState graph) :=
    (RecoveryState.FailureCoverage.initial inputs).suffixRecord
  exact ⟨⟨RecoveryState.FailureCoverage.initial inputs,
      RecoveryState.FailureCoverage.initial inputs, Finset.Subset.refl _⟩, record, record⟩

/-- The saved excluded set has the same actual archived witnesses throughout
the current attempt; its remaining witnesses lie in the saved native prefix. -/
theorem ArchivedExclusions.saved_eq {state : PhaseRuntimeState graph}
    (valid : state.ArchivedExclusions) :
    state.entry.excluded = archivedFailureOwners state.retired ∪
      state.entry.native.failureOwners := valid.saved.failureOwners_union

end PhaseRuntimeState

/-- Every primitive raw operation preserves the public failure witnesses of
all permanent exclusions, including those removed from the live store. -/
theorem phaseApplication_archivedExclusions (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.ArchivedExclusions where
  submit state who material valid :=
    ⟨(phaseApplication_failureCoverage runtime leaks).submit _ _ _ valid.coverage,
      valid.saved, valid.active.submit who material⟩
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_archivedExclusions
      exact ⟨⟨valid.coverage.saved,
          valid.coverage.active.inclusionResult runtime _ native handled,
          valid.coverage.inherited.trans (state.current.inclusionResult_excluded_subset _ _)⟩,
        valid.saved, valid.active.inclusionResult runtime _ native handled⟩
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_archivedExclusions
      exact ⟨⟨valid.coverage.saved,
          valid.coverage.active.environmentResult runtime command native supported,
          valid.coverage.inherited.trans (state.current.environmentResult_excluded_subset _ _)⟩,
        valid.saved, valid.active.environmentResult runtime command native supported⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Actual initialized raw histories retain a public witness for every saved
exclusion, either in a retired attempt or in the saved native prefix. -/
theorem phaseArchivedExclusions_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.ArchivedExclusions :=
  (phaseApplication_archivedExclusions runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_archivedExclusions plan draw) trace

end Vegas.EventGraphRuntime
