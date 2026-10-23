/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhasePlanSuffix

/-! # Completed events and surviving owners in actual retired commitment phases -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Every archive closes an original commitment phase. Its public failures
remain covered by the permanent exclusion set even after rollback. -/
def RetiredPhaseResults (plan : RuntimePhasePlan graph) (excluded : Finset Player)
    (retired : List (RetiredCommitAttempt graph)) : Prop :=
  ∀ record ∈ retired, ∃ phase ∈ plan.phases,
    record.attempt.phase = phase.low ∧ phase.kind = .commitment ∧
      phase.events ⊆ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
      ∀ event owner, graph.actor? event = some owner → record.state.PublicFailure event →
        owner ∈ excluded

omit [DecidableEq Player] in
/-- Permanent exclusion can grow without invalidating an archived result. -/
theorem RetiredPhaseResults.mono {plan : RuntimePhasePlan graph}
    {first second : Finset Player} {retired : List (RetiredCommitAttempt graph)}
    (valid : RetiredPhaseResults plan first retired) (contains : first ⊆ second) :
    RetiredPhaseResults plan second retired := by
  intro record member
  obtain ⟨phase, installed, low, kind, completed, receipts, failed⟩ := valid record member
  exact ⟨phase, installed, low, kind, completed, receipts,
    fun event owner acting failure => contains (failed event owner acting failure)⟩

/-- Actual settlement archives only finished commitment phases, retaining
their complete receipts and permanent failure coverage in every branch. -/
theorem settle_retiredPhaseResults (plan : RuntimePhasePlan graph)
    (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (installed : phases ⊆ plan.phases)
    (saved : entry.FailureCoverage) (active : current.FailureCoverage)
    (inherited : entry.excluded ⊆ current.excluded)
    (archives : RetiredPhaseResults plan current.excluded retired) :
    RetiredPhaseResults plan (settle phases generation entry current retired).current.excluded
      (settle phases generation entry current retired).retired := by
  induction phases generalizing generation entry current retired with
  | nil => exact archives
  | cons phase remaining ih =>
      have drained := active.drain phase
      have inheritedDrained : entry.excluded ⊆ (phase.drain current).excluded := by
        rw [phase.drain_excluded]
        exact inherited
      have restored := restore_failureCoverage entry (phase.drain current) saved inheritedDrained
      have rebuilt := restored.drain phase
      have tailInstalled : remaining ⊆ plan.phases :=
        fun item member => installed (List.mem_cons_of_mem phase member)
      have old : RetiredPhaseResults plan (phase.drain current).excluded retired := by
        simpa only [RuntimePhase.drain_excluded] using archives
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          have appended : RetiredPhaseResults plan (phase.drain current).excluded
              (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) := by
            intro record member
            rcases List.mem_append.mp member with prior | added
            · exact old record prior
            · have equal := List.mem_singleton.mp added
              subst record
              exact ⟨phase, installed (List.mem_cons_self ..), rfl, failure.1,
                finished, drained.receipts, drained.covered⟩
          split
          · simpa only [RuntimePhase.drain_excluded, restore] using appended
          · apply ih _ _ _ _ tailInstalled rebuilt rebuilt (Finset.Subset.refl _)
            simpa only [RuntimePhase.drain_excluded, restore] using appended
        · exact ih _ _ _ _ tailInstalled drained drained (Finset.Subset.refl _) old
      · exact old

/-- Runtime metadata needed to retain complete retired results alongside
the saved and active failure coverage. -/
structure RetiredCompletion (plan : RuntimePhasePlan graph) (state : PhaseRuntimeState graph) :
    Prop where
  suffix : state.phases <:+ plan.phases
  coverage : state.FailureCoverage
  archives : RetiredPhaseResults plan state.current.excluded state.retired

theorem initial_retiredCompletion (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    RetiredCompletion plan (initial plan inputs) := by
  refine ⟨settle_suffix .., initial_failureCoverage plan inputs, ?_⟩
  apply settle_retiredPhaseResults plan _ _ _ _ _ (fun _ member => member)
    (RecoveryState.FailureCoverage.initial inputs) (RecoveryState.FailureCoverage.initial inputs)
    (Finset.Subset.refl _)
  intro record impossible
  cases impossible

/-- With no newly excluded owner, automatic settlement changes neither the
retry generation nor the actual retired transcript. -/
theorem settle_generation_archive_of_same_excluded (phases : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph)) (same : current.excluded = entry.excluded) :
    (settle phases generation entry current retired).generation = generation ∧
      (settle phases generation entry current retired).retired = retired := by
  induction phases generalizing entry current retired with
  | nil => exact ⟨rfl, rfl⟩
  | cons phase remaining ih =>
      have noFailure : ¬ (phase.kind = .commitment ∧
          (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
        simp only [RuntimePhase.drain_excluded, same, Finset.sdiff_self,
          Finset.empty_inter, Finset.not_nonempty_empty, and_false, not_false_eq_true]
      simp only [settle, noFailure, ↓reduceIte]
      split
      · exact ih _ _ _ rfl
      · exact ⟨rfl, rfl⟩

end PhaseRuntimeState

/-- Arbitrary actual submissions, includes and scheduler commands preserve
the original finished phase and all surviving-owner archive results. -/
theorem phaseApplication_retiredCompletion (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) :
    (phaseApplication runtime leaks).Invariant (PhaseRuntimeState.RetiredCompletion plan) where
  submit state who material valid := by
    refine ⟨valid.suffix, ?_, valid.archives⟩
    exact (phaseApplication_failureCoverage runtime leaks).submit _ _ _ valid.coverage
  handle state message next valid accepted := by
    have coverage := (phaseApplication_failureCoverage runtime leaks).handle _ _ _
      valid.coverage accepted
    have suffix := (phaseApplication_planSuffix runtime leaks plan).handle _ _ _
      valid.suffix accepted
    refine ⟨suffix, coverage, ?_⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_retiredPhaseResults plan _ _ _ _ _ valid.suffix.subset
        valid.coverage.saved (valid.coverage.active.inclusionResult runtime _ native handled)
        (valid.coverage.inherited.trans (state.current.inclusionResult_excluded_subset _ _))
      exact valid.archives.mono (state.current.inclusionResult_excluded_subset _ _)
    · cases accepted
  environment state command next valid reached := by
    have coverage := (phaseApplication_failureCoverage runtime leaks).environment _ _ _
      valid.coverage reached
    have suffix := (phaseApplication_planSuffix runtime leaks plan).environment _ _ _
      valid.suffix reached
    refine ⟨suffix, coverage, ?_⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_retiredPhaseResults plan _ _ _ _ _ valid.suffix.subset
        valid.coverage.saved (valid.coverage.active.environmentResult runtime command native
          supported)
        (valid.coverage.inherited.trans (state.current.environmentResult_excluded_subset _ _))
      exact valid.archives.mono (state.current.environmentResult_excluded_subset _ _)
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid.archives

/-- Every actual initialized raw trace retains complete original phase
results and failure coverage in all its retired attempts. -/
theorem phaseRetiredCompletion_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    PhaseRuntimeState.RetiredCompletion plan control.execution.application :=
  (phaseApplication_retiredCompletion runtime leaks plan).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_retiredCompletion plan draw) trace

end Vegas.EventGraphRuntime
