/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseFrontier
import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Pending.PhaseNamespace
import Interaction.ReactiveInvariant

/-! # Recovering retired attempt completions at their source positions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RetiredCommitAttempt

/-- Reinsert a retired interval before the effective completions at its address.
The archive retains the original actions, including accepted failures. -/
def insertHistory (retired : RetiredCommitAttempt graph)
    (effective : List graph.Completion) : List graph.Completion :=
  effective.filter (fun completion => completion.event.val < retired.attempt.phase) ++
    retired.state.config.history.filter
      (fun completion => retired.attempt.phase ≤ completion.event.val) ++
    effective.filter (fun completion => retired.attempt.phase ≤ completion.event.val)

/-- A later effective suffix remains after the original retired actions. -/
theorem insertHistory_append (retired : RetiredCommitAttempt graph)
    (effective later : List graph.Completion)
    (after : ∀ completion ∈ later, retired.attempt.phase ≤ completion.event.val) :
    retired.insertHistory (effective ++ later) = retired.insertHistory effective ++ later := by
  have high : later.filter (fun completion =>
      retired.attempt.phase ≤ completion.event.val) = later := by
    exact List.filter_eq_self.mpr (fun completion member => by
      simpa only [decide_eq_true_eq] using after completion member)
  have low : later.filter (fun completion =>
      completion.event.val < retired.attempt.phase) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro completion member
    simp only [decide_eq_true_eq, not_lt]
    exact after completion member
  simp only [insertHistory, List.filter_append, low, high, List.append_nil,
    List.append_assoc]

/-- Restoring an exact semantic prefix and archiving the completed attempt
recovers its entire original completion list. -/
theorem insertHistory_of_prefix (retired : RetiredCommitAttempt graph)
    (entry : graph.Config) (saved : entry.cut.IsPrefix retired.attempt.phase)
    (retained : entry.history.IsPrefix retired.state.config.history) :
    retired.insertHistory entry.history = retired.state.config.history := by
  obtain ⟨later, complete⟩ := retained
  have low : ∀ completion ∈ entry.history,
      completion.event.val < retired.attempt.phase := by
    intro completion member
    exact (saved.2 completion.event).mp ((entry.history_exact completion.event).mp
      (List.mem_map.mpr ⟨completion, member, rfl⟩))
  have high : ∀ completion ∈ later,
      retired.attempt.phase ≤ completion.event.val := by
    intro completion member
    by_contra before
    have rank : completion.event.val < retired.attempt.phase := by omega
    have old : completion.event ∈ entry.history.map Completion.event :=
      (entry.history_exact completion.event).mpr ((saved.2 completion.event).mpr rank)
    have unique := retired.state.config.history_nodup
    rw [← complete, List.map_append, List.nodup_append] at unique
    exact unique.2.2 completion.event old completion.event
      (List.mem_map.mpr ⟨completion, member, rfl⟩) rfl
  have oldLow : entry.history.filter (fun completion =>
      completion.event.val < retired.attempt.phase) = entry.history := by
    exact List.filter_eq_self.mpr (fun completion member => by
      simpa only [decide_eq_true_eq] using low completion member)
  have oldHigh : entry.history.filter (fun completion =>
      retired.attempt.phase ≤ completion.event.val) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro completion member
    simp only [decide_eq_true_eq, not_le]
    exact low completion member
  have laterHigh : later.filter (fun completion =>
      retired.attempt.phase ≤ completion.event.val) = later := by
    exact List.filter_eq_self.mpr (fun completion member => by
      simpa only [decide_eq_true_eq] using high completion member)
  simp only [insertHistory, ← complete, List.filter_append, oldLow, oldHigh,
    laterHigh, List.nil_append, List.append_nil]

end RetiredCommitAttempt

namespace PhaseRuntimeState

/-- Recover all retired attempts in their source positions while retaining the
complete effective native history. This reads existing records only. -/
def archivedHistory (retired : List (RetiredCommitAttempt graph))
    (effective : List graph.Completion) : List graph.Completion :=
  retired.foldr RetiredCommitAttempt.insertHistory effective

/-- Without retries the recovered history is the effective history. -/
theorem archivedHistory_nil (effective : List graph.Completion) :
    archivedHistory ([] : List (RetiredCommitAttempt graph)) effective = effective := rfl

/-- Appending the newest archive inserts it before replaying older archives. -/
theorem archivedHistory_append (first second : List (RetiredCommitAttempt graph))
    (effective : List graph.Completion) :
    archivedHistory (first ++ second) effective =
      archivedHistory first (archivedHistory second effective) := by
  exact List.foldr_append

/-- A restored semantic prefix together with the new archive retains the whole
original attempt, in addition to every previous retired attempt. -/
theorem archivedHistory_retry (retired : List (RetiredCommitAttempt graph))
    (record : RetiredCommitAttempt graph) (entry : graph.Config)
    (saved : entry.cut.IsPrefix record.attempt.phase)
    (retained : entry.history.IsPrefix record.state.config.history) :
    archivedHistory (retired ++ [record]) entry.history =
      archivedHistory retired record.state.config.history := by
  rw [archivedHistory_append]
  change archivedHistory retired (record.insertHistory entry.history) = _
  rw [record.insertHistory_of_prefix entry saved retained]

/-- New effective completions after every retired address are appended after
all recovered own-attempt records, without discarding any earlier retry. -/
theorem archivedHistory_extend (retired : List (RetiredCommitAttempt graph))
    (effective later : List graph.Completion)
    (after : ∀ record ∈ retired, ∀ completion ∈ later,
      record.attempt.phase ≤ completion.event.val) :
    archivedHistory retired (effective ++ later) =
      archivedHistory retired effective ++ later := by
  induction retired with
  | nil => rfl
  | cons record rest ih =>
      change record.insertHistory (archivedHistory rest (effective ++ later)) = _
      rw [ih (fun other member => after other (List.mem_cons_of_mem _ member))]
      exact record.insertHistory_append _ _
        (after record (List.mem_cons_self))


/-- Restoring archived attempts commutes with extending the real semantic
checkpoint by its newly completed suffix. -/
theorem archivedHistory_checkpoint_extension
    (retired : List (RetiredCommitAttempt graph)) (entry current : graph.Config) (offset : Nat)
    (before : ∀ record ∈ retired, record.attempt.phase ≤ offset)
    (saved : entry.cut.IsPrefix offset) (retained : entry.history.IsPrefix current.history) :
    archivedHistory retired current.history = archivedHistory retired entry.history ++
      current.history.drop entry.history.length := by
  obtain ⟨later, complete⟩ := retained
  have high : ∀ completion ∈ later, offset ≤ completion.event.val := by
    intro completion member
    by_contra before
    have rank : completion.event.val < offset := by omega
    have old : completion.event ∈ entry.history.map Completion.event :=
      (entry.history_exact completion.event).mpr ((saved.2 completion.event).mpr rank)
    have unique := current.history_nodup
    rw [← complete, List.map_append, List.nodup_append] at unique
    exact unique.2.2 completion.event old completion.event
      (List.mem_map.mpr ⟨completion, member, rfl⟩) rfl
  rw [← complete, archivedHistory_extend retired entry.history later
    (fun record member completion present =>
      (before record member).trans (high completion present))]
  simp only [List.drop_left]

variable [DecidableEq Player]

/-- A genuine retry archives the original completed attempt before resetting
its effective history. The recovered list does not lose the voided actions. -/
theorem settle_retry_archivedHistory
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (saved : entry.native.config.cut.IsPrefix phase.low)
    (retained : entry.native.config.history.IsPrefix current.native.config.history)
    (finished : phase.Finished (phase.drain current)) (kind : phase.kind = .commitment)
    (missed : (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty)
    (survives : (phase.owners \ (phase.drain current).excluded).Nonempty) :
    let next := settle (phase :: remaining) generation entry current retired
    archivedHistory next.retired next.entry.native.config.history =
      archivedHistory retired (phase.drain current).native.config.history := by
  dsimp only
  rw [settle_retry phase remaining generation entry current retired finished kind missed survives]
  exact archivedHistory_retry retired
    ⟨⟨phase.low, generation⟩, (phase.drain current).native⟩ entry.native.config saved
      (retained.trans (phase.drain_history_prefix current))

/-- Every retired attempt precedes the current static phase address. -/
def ArchivesBefore (state : PhaseRuntimeState graph) : Prop :=
  ∀ record ∈ state.retired, record.attempt.phase ≤ state.attempt.phase

/-- Settlement retains the physical static order of every archived attempt. -/
theorem settle_archivesBefore (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (ordered : phases.IsChain fun before after => before.high = after.low)
    (before : ArchivesBefore (⟨phases, generation, entry, current, retired⟩ :
      PhaseRuntimeState graph)) :
    ArchivesBefore (settle phases generation entry current retired) := by
  induction phases generalizing generation entry current retired with
  | nil => exact before
  | cons phase remaining ih =>
      have tailLower : phase.low ≤ phaseLow remaining := by
        exact phaseLow_suffix ordered (List.suffix_cons phase remaining)
      have oldTail : ∀ record ∈ retired, record.attempt.phase ≤ phaseLow remaining := by
        intro record member
        exact (before record member).trans tailLower
      have archiveTail : ∀ record ∈ retired ++
          [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩],
          record.attempt.phase ≤ phaseLow remaining := by
        intro record member
        rcases List.mem_append.mp member with old | new
        · exact oldTail record old
        · obtain rfl := List.mem_singleton.mp new
          exact tailLower
      simp only [settle]
      split
      · split
        · split
          · intro record member
            rcases List.mem_append.mp member with old | new
            · exact before record old
            · obtain rfl := List.mem_singleton.mp new
              exact Nat.le_refl _
          · exact ih _ _ _ _ ordered.tail archiveTail
        · exact ih _ _ _ _ ordered.tail oldTail
      · exact before

/-- Every authentic application transition preserves the archive order,
including arbitrary raw submissions, inclusions and environment commands. -/
theorem archivesBefore_invariant (runtime : EventGraphRuntime graph)
    (leaks : Interaction.MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state => state.Ordered ∧ state.ArchivesBefore)
    where
  submit state who material valid := by
    exact ⟨valid.1, valid.2⟩
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact ⟨settle_ordered _ _ _ _ _ valid.1, settle_archivesBefore _ _ _ _ _ valid.1 valid.2⟩
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact ⟨settle_ordered _ _ _ _ _ valid.1, settle_archivesBefore _ _ _ _ _ valid.1 valid.2⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Actual initialized phase histories retain every archive before the current
address. Neither source alignment nor a prescribed player policy is assumed. -/
theorem archivesBefore_history (runtime : EventGraphRuntime graph)
    (leaks : Interaction.MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.ArchivesBefore := by
  have invariant := archivesBefore_invariant runtime leaks
  have result := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · exact result.2
  · obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨initial_ordered plan input,
      settle_archivesBefore _ _ _ _ _ plan.adjacent (fun _ impossible => by cases impossible)⟩

end PhaseRuntimeState
end Vegas.EventGraphRuntime
