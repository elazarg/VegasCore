/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSavedExclusionReadback
import Vegas.Pending.PhaseRetiredCompletion
import Vegas.Pending.PhasePacketAddress

/-! # Retry generations read from the public chronological archive -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace RuntimePhasePlan

omit [DecidableEq Player] [Fintype Player] in
/-- A static phase boundary identifies its whole descriptor, including all
original owners; different private values cannot change that descriptor. -/
theorem phase_eq_of_low_eq (plan : RuntimePhasePlan graph) (first second : RuntimePhase graph)
    (firstMember : first ∈ plan.phases) (secondMember : second ∈ plan.phases)
    (same : first.low = second.low) : first = second := by
  let event : graph.EventId := ⟨first.low, first.nonempty.trans_le first.bounded⟩
  apply containing_unique plan.phases plan.adjacent event first second firstMember secondMember
  · exact (first.mem_events event).mpr ⟨le_rfl, first.nonempty⟩
  · exact (second.mem_events event).mpr ⟨by simpa only [event, same] using le_rfl,
      by simpa only [event, same] using second.nonempty⟩

end RuntimePhasePlan

namespace PhaseRuntimeState

/-- A retired attempt retries precisely when its static commitment block has
an original owner outside the exclusions reconstructed at that actual close. -/
def RetiredRetry (plan : RuntimePhasePlan graph) (endingExcluded : Finset Player)
    (record : RetiredCommitAttempt graph) : Prop :=
  ∃ phase ∈ plan.phases, phase.low = record.attempt.phase ∧ phase.kind = .commitment ∧
    (phase.owners \ endingExcluded).Nonempty

open scoped Classical in
/-- Read retry-causing attempt identifiers in their original archive order.
The running exclusion fold includes this record before testing its survivors. -/
def archivedRetryAttemptsFrom (plan : RuntimePhasePlan graph) (inherited : Finset Player) :
    List (RetiredCommitAttempt graph) → List CommitAttemptId
  | [] => []
  | record :: rest =>
      let endingExcluded := inherited ∪ record.state.failureOwners
      (if RetiredRetry plan endingExcluded record then [record.attempt] else []) ++
        archivedRetryAttemptsFrom plan endingExcluded rest

/-- The public retry readout starts with the original empty excluded set. -/
def archivedRetryAttempts (plan : RuntimePhasePlan graph)
    (retired : List (RetiredCommitAttempt graph)) : List CommitAttemptId :=
  archivedRetryAttemptsFrom plan ∅ retired

open scoped Classical in
/-- Generation immediately before each archive is the preceding retry count.
An exhausted close remains at that generation instead of consuming a retry. -/
def ArchiveGenerationFrom (plan : RuntimePhasePlan graph) (inherited : Finset Player)
    (generation : Nat) : List (RetiredCommitAttempt graph) → Prop
  | [] => True
  | record :: rest =>
      record.attempt.generation = generation ∧
        ArchiveGenerationFrom plan (inherited ∪ record.state.failureOwners)
          (generation + if RetiredRetry plan (inherited ∪ record.state.failureOwners) record
            then 1 else 0) rest

/-- Actual retired namespace tags and current generation agree with exactly
the retry-causing public archive records. -/
def ArchiveGeneration (plan : RuntimePhasePlan graph) (state : PhaseRuntimeState graph) : Prop :=
  ArchiveGenerationFrom plan ∅ 0 state.retired ∧
    (archivedRetryAttempts plan state.retired).map CommitAttemptId.generation =
      List.range state.generation

theorem archivedRetryAttemptsFrom_append (plan : RuntimePhasePlan graph)
    (inherited : Finset Player) (first second : List (RetiredCommitAttempt graph)) :
    archivedRetryAttemptsFrom plan inherited (first ++ second) =
      archivedRetryAttemptsFrom plan inherited first ++
        archivedRetryAttemptsFrom plan (inherited ∪ archivedFailureOwners first) second := by
  classical
  induction first generalizing inherited with
  | nil => simp only [List.nil_append, archivedRetryAttemptsFrom, List.nil_append,
      archivedFailureOwners, List.foldr_nil, Finset.union_empty]
  | cons record rest ih =>
      simp only [List.cons_append, archivedRetryAttemptsFrom, ih, archivedFailureOwners,
        List.foldr_cons, Finset.union_assoc, List.append_assoc]

theorem archiveGenerationFrom_append (plan : RuntimePhasePlan graph)
    (inherited : Finset Player) (generation : Nat)
    (first second : List (RetiredCommitAttempt graph)) :
    ArchiveGenerationFrom plan inherited generation (first ++ second) ↔
      ArchiveGenerationFrom plan inherited generation first ∧
        ArchiveGenerationFrom plan (inherited ∪ archivedFailureOwners first)
          (generation + (archivedRetryAttemptsFrom plan inherited first).length) second := by
  classical
  induction first generalizing inherited generation with
  | nil => simp only [List.nil_append, ArchiveGenerationFrom, archivedFailureOwners,
      List.foldr_nil, Finset.union_empty, archivedRetryAttemptsFrom, List.length_nil,
      Nat.add_zero, true_and]
  | cons record rest ih =>
      simp only [List.cons_append, ArchiveGenerationFrom]
      rw [ih]
      simp only [archivedFailureOwners, List.foldr_cons, Finset.union_assoc,
        archivedRetryAttemptsFrom, List.length_append]
      split_ifs <;> simp only [List.length_singleton, List.length_nil, Nat.add_zero,
        Nat.zero_add, Nat.add_assoc, and_assoc]

omit [Fintype Player] in
private theorem retiredRetry_of_phase (plan : RuntimePhasePlan graph)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (kind : phase.kind = .commitment) (endingExcluded : Finset Player)
    (generation : Nat) (native : State graph) :
    RetiredRetry plan endingExcluded ⟨⟨phase.low, generation⟩, native⟩ ↔
      (phase.owners \ endingExcluded).Nonempty := by
  constructor
  · rintro ⟨other, otherMember, same, _otherKind, survivors⟩
    have equal := plan.phase_eq_of_low_eq other phase otherMember member same
    exact equal ▸ survivors
  · intro survivors
    exact ⟨phase, member, rfl, kind, survivors⟩

private theorem archivedRetryAttempts_append_actual (plan : RuntimePhasePlan graph)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (kind : phase.kind = .commitment) (generation : Nat)
    (current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (failures : SuffixExclusionRecord 0 (archivedFailureOwners retired) current) :
    archivedRetryAttempts plan
        (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) =
      archivedRetryAttempts plan retired ++
        if (phase.owners \ current.excluded).Nonempty then [⟨phase.low, generation⟩] else [] := by
  have ending := (failures.phase_drain phase).failureOwners_union.symm
  unfold archivedRetryAttempts
  rw [archivedRetryAttemptsFrom_append]
  simp only [Finset.empty_union, archivedRetryAttemptsFrom, List.append_nil]
  rw [Finset.empty_union, ending, RuntimePhase.drain_excluded,
    retiredRetry_of_phase plan phase member kind]
  split_ifs <;> rfl

/-- Actual normalization appends at most one old attempt before entering a
fresh phase. The public retry readout distinguishes retry from exhaustion. -/
theorem settle_archiveGeneration (plan : RuntimePhasePlan graph)
    (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (suffix : phases <:+ plan.phases)
    (failures : SuffixExclusionRecord 0 (archivedFailureOwners retired) current)
    (prior : ArchiveGeneration plan ⟨phases, generation, entry, current, retired⟩) :
    ArchiveGeneration plan (settle phases generation entry current retired) := by
  classical
  cases phases with
  | nil => exact prior
  | cons phase remaining =>
      have member : phase ∈ plan.phases := suffix.subset List.mem_cons_self
      have count : (archivedRetryAttempts plan retired).length = generation := by
        have sizes := congrArg List.length prior.2
        simpa only [List.length_map, List.length_range] using sizes
      have appendValid : ArchiveGenerationFrom plan ∅ 0
          (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) := by
        rw [archiveGenerationFrom_append]
        refine ⟨prior.1, ?_⟩
        change generation = 0 + (archivedRetryAttemptsFrom plan ∅ retired).length ∧ True
        exact ⟨by simpa only [archivedRetryAttempts, Nat.zero_add] using count.symm, trivial⟩
      simp only [settle]
      split
      · split
        · rename_i missed
          have appendIds := archivedRetryAttempts_append_actual plan phase member missed.1
            generation current retired failures
          split
          · rename_i survivors
            refine ⟨appendValid, ?_⟩
            change (archivedRetryAttempts plan
              (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩])).map
                CommitAttemptId.generation = List.range (generation + 1)
            rw [appendIds,
              ite_eq_left (by simpa only [RuntimePhase.drain_excluded] using survivors)]
            simpa only [List.map_append, List.map_singleton, prior.2] using
              (List.range_succ (n := generation)).symm
          · rename_i exhausted
            have fresh := settle_generation_archive_of_same_excluded remaining generation
              (phase.drain (restore entry (phase.drain current)))
              (phase.drain (restore entry (phase.drain current)))
              (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) rfl
            constructor
            · rw [fresh.2]
              exact appendValid
            · rw [fresh.1, fresh.2, appendIds,
                ite_eq_right (by simpa only [RuntimePhase.drain_excluded] using exhausted),
                List.append_nil]
              exact prior.2
        · have fresh := settle_generation_archive_of_same_excluded remaining generation
            (phase.drain current) (phase.drain current) retired rfl
          constructor
          · rw [fresh.2]
            exact prior.1
          · rw [fresh.1, fresh.2]
            exact prior.2
      · exact prior

/-- Initialization has no retired attempts and consumes no retry generation. -/
theorem initial_archiveGeneration (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    ArchiveGeneration plan (initial plan inputs) := by
  have fresh := settle_generation_archive_of_same_excluded plan.phases 0
    (⟨State.initial inputs, ∅⟩ : RecoveryState graph)
    (⟨State.initial inputs, ∅⟩ : RecoveryState graph) [] rfl
  constructor
  · change ArchiveGenerationFrom plan ∅ 0 (settle _ _ _ _ _).retired
    rw [fresh.2]
    trivial
  · change (archivedRetryAttempts plan (settle _ _ _ _ _).retired).map
        CommitAttemptId.generation = List.range (settle _ _ _ _ _).generation
    rw [fresh.1, fresh.2]
    rfl

end PhaseRuntimeState

/-- Primitive physical operations preserve the retry scan together with the
actual exclusion witnesses and static phase suffix used to interpret it. -/
theorem phaseApplication_archiveGeneration (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      state.ArchivedExclusions ∧ state.phases <:+ plan.phases ∧
        state.ArchiveGeneration plan) where
  submit state who material valid :=
    ⟨(phaseApplication_archivedExclusions runtime leaks).submit _ _ _ valid.1,
      valid.2.1, valid.2.2⟩
  handle state message next valid accepted := by
    refine ⟨(phaseApplication_archivedExclusions runtime leaks).handle _ _ _ valid.1 accepted,
      (phaseApplication_planSuffix runtime leaks plan).handle _ _ _ valid.2.1 accepted, ?_⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.settle_archiveGeneration plan _ _ _ _ _ valid.2.1
        (valid.1.active.inclusionResult runtime _ native handled) valid.2.2
    · cases accepted
  environment state command next valid reached := by
    refine ⟨(phaseApplication_archivedExclusions runtime leaks).environment
        _ _ _ valid.1 reached,
      (phaseApplication_planSuffix runtime leaks plan).environment _ _ _ valid.2.1 reached, ?_⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      exact PhaseRuntimeState.settle_archiveGeneration plan _ _ _ _ _ valid.2.1
        (valid.1.active.environmentResult runtime command native supported) valid.2.2
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid.2.2

/-- Every genuine initialized history computes its current generation from
exactly the public retired records that still had a surviving phase owner. -/
theorem phaseArchiveGeneration_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.ArchiveGeneration plan :=
  ((phaseApplication_archiveGeneration runtime leaks plan).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_archivedExclusions plan draw,
        PhaseRuntimeState.settle_suffix ..,
        PhaseRuntimeState.initial_archiveGeneration plan draw⟩) trace).2.2

end Vegas.EventGraphRuntime
