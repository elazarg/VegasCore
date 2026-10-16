/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseArchivedRecall

/-! # Automatic completion preserves surviving owners' original action records -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RuntimePhase

/-- Automatic service completes only excluded owners' events and therefore
leaves every surviving owner's complete dependent action records unchanged. -/
theorem drainFuel_ownCompletions (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) (who : Player) (active : who ∉ state.excluded) :
    graph.ownCompletions who (phase.drainFuel fuel state).native.config.history =
      graph.ownCompletions who state.native.config.history := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        obtain ⟨owner, acting, excluded⟩ := (Classical.choose_spec pending).2.owned
        have different : graph.actor? (Classical.choose pending) ≠ some who := by
          intro same
          have ownerEq := Option.some.inj (acting.symm.trans same)
          subst owner
          exact active excluded
        obtain ⟨action, supported⟩ := state.native.completeFailure_step _
          (Classical.choose_spec pending).2.1 acting
        rw [ih (state.completeAutomatic (Classical.choose pending)
          (Classical.choose_spec pending).2) active]
        change graph.ownCompletions who
          (state.native.completeFailure _ _).config.history = _
        rw [state.native.config.step_history _ _ _ _ supported]
        simp only [ownCompletions, List.filter_append, List.filter_cons, List.filter_nil,
          different, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      · rfl

/-- The actual bounded automatic drain preserves every surviving own word. -/
theorem drain_ownCompletions (phase : RuntimePhase graph) (state : RecoveryState graph)
    (who : Player) (active : who ∉ state.excluded) :
    graph.ownCompletions who (phase.drain state).native.config.history =
      graph.ownCompletions who state.native.config.history :=
  phase.drainFuel_ownCompletions _ state who active

/-- An interval with no event of the focal owner contributes no new original
owned completion, even when other owners fail or are served automatically. -/
theorem ownCompletions_eq_of_unowned (phase : RuntimePhase graph)
    (entry current : graph.Config) (saved : entry.cut.IsPrefix phase.low)
    (within : current.cut.Within phase.low phase.high)
    (retained : entry.history.IsPrefix current.history) (who : Player)
    (outside : who ∉ phase.owners) :
    graph.ownCompletions who current.history = graph.ownCompletions who entry.history := by
  obtain ⟨later, complete⟩ := retained
  have empty : graph.ownCompletions who later = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro completion member
    simp only [decide_eq_true_eq]
    intro acting
    have high : completion.event.val < phase.high :=
      within.2 completion.event ((current.history_exact completion.event).mp
        (List.mem_map.mpr ⟨completion, by rw [← complete]; exact List.mem_append_right _ member,
          rfl⟩))
    have low : phase.low ≤ completion.event.val := by
      by_contra before
      have rank : completion.event.val < phase.low := by omega
      have old : completion.event ∈ entry.history.map Completion.event :=
        (entry.history_exact completion.event).mpr ((saved.2 completion.event).mpr rank)
      have unique := current.history_nodup
      rw [← complete, List.map_append, List.nodup_append] at unique
      exact unique.2.2 completion.event old completion.event
        (List.mem_map.mpr ⟨completion, member, rfl⟩) rfl
    apply outside
    apply Finset.mem_biUnion.mpr
    refine ⟨completion.event, (phase.mem_events completion.event).mpr ⟨low, high⟩, ?_⟩
    simp only [acting, Option.toFinset_some, Finset.mem_singleton]
  rw [← complete]
  change (entry.history ++ later).filter _ = _
  rw [List.filter_append]
  change graph.ownCompletions who entry.history ++ graph.ownCompletions who later = _
  rw [empty, List.append_nil]

end RuntimePhase

namespace PhaseRuntimeState

private theorem own_append (who : Player) (first second : List graph.Completion) :
    graph.ownCompletions who (first ++ second) =
      graph.ownCompletions who first ++ graph.ownCompletions who second := by
  exact List.filter_append first second

private theorem own_filter (who : Player) (past : List graph.Completion)
    (test : graph.Completion → Bool) :
    graph.ownCompletions who (past.filter test) =
      (graph.ownCompletions who past).filter test := by
  exact List.filter_comm _ _ _

/-- Archive insertion depends on the effective history only through its actual
owned completion records. Foreign automatic failures cannot alter that word. -/
theorem archivedHistory_own_congr (retired : List (RetiredCommitAttempt graph))
    (first second : List graph.Completion) (who : Player)
    (same : graph.ownCompletions who first = graph.ownCompletions who second) :
    graph.ownCompletions who (archivedHistory retired first) =
      graph.ownCompletions who (archivedHistory retired second) := by
  induction retired with
  | nil => exact same
  | cons record rest ih =>
      change graph.ownCompletions who (record.insertHistory _) =
        graph.ownCompletions who (record.insertHistory _)
      dsimp only [archivedHistory] at ih
      simp only [RetiredCommitAttempt.insertHistory, own_append, own_filter, ih]

end PhaseRuntimeState
end Vegas.EventGraphRuntime
