/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication

/-! # Exact correspondence of phase-local and global automatic completion

With unchanged exclusion at the checkpoint, phase settlement follows the same
actual automatic graph steps as forced-exit recovery. Unique readiness makes
these steps deterministic; a globally quiescent endpoint is the global drain.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RecoveryState

/-- Taking one eligible automatic step does not alter the complete drained
result when every currently eligible event is that same event. -/
theorem drain_completeAutomatic (state : RecoveryState graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event)
    (unique : ∀ other, state.AutomaticReady other → other = event) :
    state.drain = (state.completeAutomatic event eligible).drain := by
  have progress := state.completeAutomatic_progress event eligible
  unfold drain
  rw [← progress, drainFuel]
  split
  · rename_i pending
    have selected : Classical.choose pending = event :=
      unique _ (Classical.choose_spec pending)
    have same : state.completeAutomatic (Classical.choose pending)
        (Classical.choose_spec pending) = state.completeAutomatic event eligible := by
      cases selected
      rfl
    rw [same]
  · rename_i impossible
    exact (impossible ⟨event, eligible⟩).elim

/-- Actual automatic paths preserve their unique global normal form. -/
theorem drain_eq_of_automatic_path
    (unique : ∀ (cut : graph.order.Cut) {left right : graph.EventId},
      cut.Ready left → cut.Ready right → left = right)
    {before after : RecoveryState graph}
    (path : Relation.ReflTransGen AutomaticStep before after) : before.drain = after.drain := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head before middle moved _ ih =>
      obtain ⟨event, eligible, rfl⟩ := moved
      exact (before.drain_completeAutomatic event eligible
        (fun other otherReady => unique _ otherReady.1 eligible.1)).trans ih

end RecoveryState

namespace RuntimePhase

/-- A phase drain's existing native trace is also a global automatic trace. -/
theorem drain_automatic_trace (phase : RuntimePhase graph) (state : RecoveryState graph) :
    Relation.ReflTransGen RecoveryState.AutomaticStep state (phase.drain state) := by
  refine Relation.ReflTransGen.mono ?_ _ _ (phase.drain_trace state)
  intro before after moved
  obtain ⟨event, eligible, rfl⟩ := moved
  exact ⟨event, eligible.2, rfl⟩

end RuntimePhase

namespace PhaseRuntimeState

/-- If no exclusion is new at the checkpoint, settlement performs only the
actual automatic completions; no rollback or archive update is required. -/
theorem settle_current_automatic_trace (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (sameExcluded : entry.excluded = current.excluded) :
    Relation.ReflTransGen RecoveryState.AutomaticStep current
      (settle phases generation entry current retired).current := by
  induction phases generalizing generation entry current retired with
  | nil => exact .refl
  | cons phase remaining ih =>
      have clean : ¬ (phase.kind = .commitment ∧
          (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
        rw [phase.drain_excluded, ← sameExcluded]
        simp only [Finset.sdiff_self, Finset.empty_inter, Finset.not_nonempty_empty, and_false,
          not_false_eq_true]
      by_cases finished : phase.Finished (phase.drain current)
      · rw [settle_clean phase remaining generation entry current retired finished clean]
        exact (phase.drain_automatic_trace current).trans (ih _ _ _ _ rfl)
      · simpa only [settle, finished, ↓reduceIte] using phase.drain_automatic_trace current

/-- Unique readiness and the actual endpoint's quiescence identify phase
settlement with the existing global forced-exit drain, including all state fields. -/
theorem settle_current_eq_drain (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (sameExcluded : entry.excluded = current.excluded)
    (unique : ∀ (cut : graph.order.Cut) {left right : graph.EventId},
      cut.Ready left → cut.Ready right → left = right)
    (quiescent : ∀ event,
      ¬ (settle phases generation entry current retired).current.AutomaticReady event) :
    (settle phases generation entry current retired).current = current.drain := by
  have path := settle_current_automatic_trace phases generation entry current retired sameExcluded
  have equal := RecoveryState.drain_eq_of_automatic_path unique path
  rw [RecoveryState.drain_eq_of_clear _ quiescent] at equal
  exact equal.symm

end PhaseRuntimeState

end Vegas.EventGraphRuntime
