/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearHistory
import Vegas.Pending.PhaseFrontier

/-! # Exact clear settlement at completed and fresh phase frontiers -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- No owner is eligible for automatic completion before any exclusion. -/
theorem RuntimePhase.drain_of_no_exclusions (phase : RuntimePhase graph)
    (state : RecoveryState graph) (clear : state.excluded = ∅) : phase.drain state = state := by
  apply phase.drain_eq_of_clear state
  rintro event ⟨_inside, automatic⟩
  obtain ⟨owner, _acting, excluded⟩ := automatic.owned
  simp only [clear, Finset.notMem_empty] at excluded

namespace PhaseRuntimeState

/-- A newly installed clear phase has no completed event in its own interval,
so settlement retains its exact saved state and descriptor. -/
theorem settle_at_clear_entry (phases : List (RuntimePhase graph)) (generation : Nat)
    (state : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (clear : state.excluded = ∅)
    (atStart : ∀ phase ∈ phases.head?, state.native.config.cut.IsPrefix phase.low) :
    settle phases generation state state retired = ⟨phases, generation, state, state, retired⟩ := by
  classical
  cases phases with
  | nil => rfl
  | cons phase remaining =>
      have completedPrefix := atStart phase (by simp only [List.head?_cons, Option.mem_some_iff])
      let event : graph.EventId := ⟨phase.low, phase.nonempty.trans_le phase.bounded⟩
      have inside : event ∈ phase.events := (phase.mem_events event).mpr ⟨le_rfl, phase.nonempty⟩
      have unfinished : ¬ phase.Finished state := by
        intro finished
        have before := (completedPrefix.2 event).mp (finished inside)
        exact (Nat.lt_irrefl phase.low) before
      simp only [settle, phase.drain_of_no_exclusions state clear, unfinished, ↓reduceIte]

/-- At an actual clear frontier, finishing the head phase installs exactly its
successor. No second phase can already be complete at its fresh lower cut. -/
theorem normalize_of_clear_finished (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : state.phases = phase :: remaining) (frontier : state.Frontier)
    (clear : state.current.excluded = ∅) (finished : phase.Finished state.current) :
    state.normalize = ⟨remaining, state.generation, state.current, state.current,
      state.retired⟩ := by
  classical
  have within := frontier.positioned
  rw [installed] at within
  have completedPrefix := phase.finished_prefix state.current within.2 finished
  have next : settle remaining state.generation state.current state.current state.retired =
      ⟨remaining, state.generation, state.current, state.current, state.retired⟩ := by
    apply settle_at_clear_entry remaining state.generation state.current state.retired clear
    intro following member
    cases remaining with
    | nil => cases member
    | cons followingHead tail =>
        have same : followingHead = following := by
          simpa only [List.head?_cons, Option.mem_some_iff] using member
        subst following
        have adjacent := frontier.adjacent
        rw [installed] at adjacent
        have boundary := adjacent.rel_head? (y := followingHead) (by simp)
        rw [← boundary]
        exact completedPrefix
  have clean : ¬ ((state.current.excluded \ state.entry.excluded) ∩ phase.owners).Nonempty := by
    simp only [clear, Finset.empty_sdiff, Finset.empty_inter, Finset.not_nonempty_empty,
      not_false_eq_true]
  unfold normalize
  rw [installed]
  simp only [settle, phase.drain_of_no_exclusions state.current clear, finished, clean,
    and_false, ↓reduceIte]
  exact next

end PhaseRuntimeState
end Vegas.EventGraphRuntime
