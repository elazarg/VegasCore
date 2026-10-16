/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseArchivedRecall
import Vegas.Pending.PhaseExclusionRecord
import Vegas.EventGraph.ConfigRestriction

/-! # Original owned prefixes shared by every retired native observation -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem own_before_saved (entry current : graph.Config) (low cutoff : Nat)
    (saved : entry.cut.IsPrefix low) (retained : entry.history.IsPrefix current.history)
    (bounded : cutoff ≤ low) (who : Player) :
    (graph.ownCompletions who current.history).filter
        (fun completion => completion.event.val < cutoff) =
      (graph.ownCompletions who entry.history).filter
        (fun completion => completion.event.val < cutoff) := by
  have recall : (graph.ownCompletions who entry.history).IsPrefix
      (graph.ownCompletions who current.history) := by
    obtain ⟨later, complete⟩ := retained
    rw [← complete]
    simp only [ownCompletions, List.filter_append]
    exact ⟨_, rfl⟩
  have old := Config.ownCompletions_filter_eq_of_prefix entry current who recall
  have restricted := congrArg (List.filter fun completion : graph.Completion =>
    completion.event.val < cutoff) old
  have erase : ((graph.ownCompletions who current.history).filter
      (fun completion => completion.event ∈ entry.cut.completed)).filter
        (fun completion => completion.event.val < cutoff) =
      (graph.ownCompletions who current.history).filter
        (fun completion => completion.event.val < cutoff) := by
    simp only [List.filter_filter]
    apply List.filter_congr
    intro completion member
    by_cases before : completion.event.val < cutoff
    · have completed := (saved.2 completion.event).mpr (by omega)
      simp only [before, completed, decide_true, Bool.and_true]
    · simp only [before, decide_false, Bool.false_and]
  rw [erase] at restricted
  exact restricted

namespace PhaseRuntimeState

/-- Below an archived attempt's lower address, its original owned records are
exactly the permanent effective prefix retained by the current native state. -/
def RetiredOwnPrefix (current : State graph) (retired : List (RetiredCommitAttempt graph)) : Prop :=
  ∀ record ∈ retired, ∀ who,
    (graph.ownCompletions who record.state.config.history).filter
        (fun completion => completion.event.val < record.attempt.phase) =
      (graph.ownCompletions who current.config.history).filter
        (fun completion => completion.event.val < record.attempt.phase)

private theorem RetiredOwnPrefix.rebase {before after : State graph}
    {retired : List (RetiredCommitAttempt graph)} (valid : RetiredOwnPrefix before retired)
    (entry : graph.Config) (low : Nat) (saved : entry.cut.IsPrefix low)
    (first : entry.history.IsPrefix before.config.history)
    (second : entry.history.IsPrefix after.config.history)
    (bounded : ∀ record ∈ retired, record.attempt.phase ≤ low) :
    RetiredOwnPrefix after retired := by
  intro record member who
  exact (valid record member who).trans
    ((own_before_saved entry before.config low record.attempt.phase saved first
      (bounded record member) who).trans
        (own_before_saved entry after.config low record.attempt.phase saved second
          (bounded record member) who).symm)

private theorem RetiredOwnPrefix.extend {state : PhaseRuntimeState graph}
    (valid : RetiredOwnPrefix state.current.native state.retired)
    (frontier : state.Frontier) (history : state.HistoryCheckpoint)
    (before : state.ArchivesBefore) (next : State graph)
    (retained : state.current.native.config.history.IsPrefix next.config.history) :
    RetiredOwnPrefix next state.retired := by
  cases phases : state.phases with
  | nil =>
      have saved := frontier.positioned
      rw [phases] at saved
      apply valid.rebase state.current.native.config graph.order.eventCount saved
        (by exact ⟨[], by simp only [List.append_nil]⟩) retained
      intro record member
      simpa only [attempt, phases, List.head?_nil, Option.map_none, Option.getD_none] using
        before record member
  | cons phase remaining =>
      have saved := frontier.positioned
      rw [phases] at saved
      apply valid.rebase state.entry.native.config phase.low saved.1 history
        (history.trans retained)
      intro record member
      simpa only [attempt, phases, List.head?_cons, Option.map_some, Option.getD_some] using
        before record member

/-- Real settlement preserves all archived saved prefixes and records the exact
old prefix of a newly retired attempt, including after automatic exhaustion. -/
theorem settle_retiredOwnPrefix (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (frontier : Frontier (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph))
    (history : entry.native.config.history.IsPrefix current.native.config.history)
    (before : ArchivesBefore (⟨phases, generation, entry, current, retired⟩ :
      PhaseRuntimeState graph)) (archives : RetiredOwnPrefix current.native retired) :
    RetiredOwnPrefix (settle phases generation entry current retired).current.native
      (settle phases generation entry current retired).retired := by
  induction phases generalizing generation entry current retired with
  | nil => exact archives
  | cons phase remaining ih =>
      obtain ⟨adjacent, last, saved, within⟩ := frontier
      have bound : ∀ record ∈ retired, record.attempt.phase ≤ phase.low := before
      have drainedHistory := history.trans (phase.drain_history_prefix current)
      have rebuiltHistory : entry.native.config.history.IsPrefix
          (phase.drain (restore entry (phase.drain current))).native.config.history := by
        simpa only [restore] using
          phase.drain_history_prefix (restore entry (phase.drain current))
      have drainedArchives := archives.rebase entry.native.config phase.low saved history
        drainedHistory bound
      have rebuiltArchives := archives.rebase entry.native.config phase.low saved history
        rebuiltHistory bound
      have recorded : RetiredOwnPrefix
          (phase.drain (restore entry (phase.drain current))).native
          (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) := by
        intro record member who
        rcases List.mem_append.mp member with old | new
        · exact rebuiltArchives record old who
        · obtain rfl := List.mem_singleton.mp new
          exact (own_before_saved entry.native.config (phase.drain current).native.config
            phase.low phase.low saved drainedHistory (Nat.le_refl _) who).trans
            (own_before_saved entry.native.config
              (phase.drain (restore entry (phase.drain current))).native.config phase.low phase.low
              saved rebuiltHistory (Nat.le_refl _) who).symm
      have tailLower : phase.low ≤ phaseLow remaining :=
        phaseLow_suffix adjacent (List.suffix_cons phase remaining)
      have oldTail : ∀ record ∈ retired, record.attempt.phase ≤ phaseLow remaining :=
        fun record member => (bound record member).trans tailLower
      have newTail : ∀ record ∈ retired ++
          [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩],
          record.attempt.phase ≤ phaseLow remaining := by
        intro record member
        rcases List.mem_append.mp member with old | new
        · exact oldTail record old
        · obtain rfl := List.mem_singleton.mp new
          exact tailLower
      have drainedWithin := phase.drain_within current within
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          have restoredWithin : (restore entry (phase.drain current)).native.config.cut.Within
              phase.low phase.high := saved.within phase.nonempty.le
          have rebuiltWithin := phase.drain_within (restore entry (phase.drain current))
            restoredWithin
          split
          · exact recorded
          · rename_i exhausted
            have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
              intro owner member
              by_contra missing
              exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨member, missing⟩⟩
            have completed := phase.drain_finished_of_excluded
              (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
            have next := positioned_next phase remaining _ adjacent last
              (phase.finished_prefix _ rebuiltWithin completed)
            exact ih _ _ _ _ ⟨next.adjacent, next.last, next.positioned⟩
              (by exact ⟨[], by simp only [List.append_nil]⟩) newTail recorded
        · have next := positioned_next phase remaining _ adjacent last
            (phase.finished_prefix _ drainedWithin finished)
          exact ih _ _ _ _ ⟨next.adjacent, next.last, next.positioned⟩
            (by exact ⟨[], by simp only [List.append_nil]⟩) oldTail drainedArchives
      · exact drainedArchives

end PhaseRuntimeState

/-- Every authentic physical operation preserves old owned prefixes at each
archived attempt address; rollback removes only the current attempt suffix. -/
theorem phaseApplication_retiredOwnPrefix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      state.Frontier ∧ state.HistoryCheckpoint ∧ state.ArchivesBefore ∧
        PhaseRuntimeState.RetiredOwnPrefix state.current.native state.retired) where
  submit state who material valid := by
    refine ⟨PhaseRuntimeState.submit_frontier state who material valid.1,
      (phaseApplication_historyCheckpoint runtime leaks).submit state who material valid.2.1,
      valid.2.2.1, ?_⟩
    apply valid.2.2.2.extend valid.1 valid.2.1 valid.2.2.1
    change state.current.native.config.history.IsPrefix
      (submitStep (material.call.register state.current.native who) who
        material.call.packet).config.history
    rw [submitStep_config, (material.call.register_facts who state.current.native).1]
  handle state message next valid accepted := by
    refine ⟨PhaseRuntimeState.handle_frontier runtime state next message valid.1 accepted,
      (phaseApplication_historyCheckpoint runtime leaks).handle state message next valid.2.1
        accepted,
      ((PhaseRuntimeState.archivesBefore_invariant runtime leaks).handle state message next
        ⟨valid.1.adjacent, valid.2.2.1⟩ accepted).2, ?_⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      obtain ⟨event, _named, ready, action, supported⟩ :=
        handle_config_mem_step runtime state.current.native native _ handled
      have retained : state.current.native.config.history.IsPrefix native.config.history := by
        rw [state.current.native.config.step_history event ready action native.config supported]
        exact ⟨_, rfl⟩
      exact PhaseRuntimeState.settle_retiredOwnPrefix _ _ _ _ _
        (PhaseRuntimeState.raw_handle_frontier runtime state valid.1 _ native authorized handled)
        (valid.2.1.trans retained) valid.2.2.1
        (valid.2.2.2.extend valid.1 valid.2.1 valid.2.2.1 native retained)
    · cases accepted
  environment state command next valid reached := by
    refine ⟨PhaseRuntimeState.environment_frontier runtime state next command valid.1 reached,
      (phaseApplication_historyCheckpoint runtime leaks).environment state command next valid.2.1
        reached,
      ((PhaseRuntimeState.archivesBefore_invariant runtime leaks).environment state command next
        ⟨valid.1.adjacent, valid.2.2.1⟩ reached).2, ?_⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      have retained := environmentStep_history_prefix runtime state.current.native native command
        supported
      exact PhaseRuntimeState.settle_retiredOwnPrefix _ _ _ _ _
        (PhaseRuntimeState.raw_environment_frontier runtime state valid.1 _ native
          allowed supported)
        (valid.2.1.trans retained) valid.2.2.1
        (valid.2.2.2.extend valid.1 valid.2.1 valid.2.2.1 native retained)
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid.2.2.2

/-- Each archived owned prefix is readable from the genuine current own action
word, at arbitrary initialized raw histories and permanent exclusions. -/
theorem phaseRetiredOwnPrefix_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    PhaseRuntimeState.RetiredOwnPrefix control.execution.application.current.native
      control.execution.application.retired := by
  have invariant := phaseApplication_retiredOwnPrefix runtime leaks
  have result := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · exact result.2.2.2
  · obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    refine ⟨PhaseRuntimeState.initial_frontier plan input,
      PhaseRuntimeState.initial_historyCheckpoint plan input, ?_, ?_⟩
    · exact PhaseRuntimeState.settle_archivesBefore _ _ _ _ _ plan.adjacent
        (fun _ impossible => by cases impossible)
    · exact PhaseRuntimeState.settle_retiredOwnPrefix _ _ _ _ _
        (PhaseRuntimeState.initial_checkpoint_frontier plan input)
        (by exact ⟨[], by simp only [List.append_nil]⟩)
        (fun _ impossible => by cases impossible) (fun _ impossible => by cases impossible)

end Vegas.EventGraphRuntime
