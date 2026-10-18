/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedBudget
import Vegas.Pending.PhaseServiceProgress
import Vegas.Pending.PhaseResolution

/-! # Finite semantic work across physical phase retries

The bound counts namespace progress and genuine event completion, not padded
scheduler commands or submissions. It can therefore be fixed before choosing
the reserved packet capacity and the physical execution horizon.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def workRemaining (state : PhaseRuntimeState graph) : Nat :=
  (graph.order.eventCount + Fintype.card Player -
      (state.attempt.phase + state.attempt.generation)) * (graph.order.eventCount + 1) +
    state.current.native.config.remaining

def workBound (graph : Vegas.EventGraph Player L) : Nat :=
  (graph.order.eventCount + Fintype.card Player) * (graph.order.eventCount + 1) +
    graph.order.eventCount

omit [DecidableEq Player] in
theorem workRemaining_le_bound (state : PhaseRuntimeState graph) :
    workRemaining state ≤ workBound graph := by
  have capacity := Nat.mul_le_mul_right (graph.order.eventCount + 1)
    (Nat.sub_le (graph.order.eventCount + Fintype.card Player)
      (state.attempt.phase + state.attempt.generation))
  exact Nat.add_le_add capacity (Nat.sub_le _ _)

omit [DecidableEq Player] in
theorem work_decreases_of_namespace (before after : PhaseRuntimeState graph)
    (phase : before.attempt.phase ≤ after.attempt.phase)
    (generation : before.attempt.generation ≤ after.attempt.generation)
    (phaseBound : after.attempt.phase ≤ graph.order.eventCount)
    (generationBound : after.attempt.generation ≤ Fintype.card Player)
    (different : before.attempt ≠ after.attempt) : workRemaining after < workRemaining before := by
  have strict : before.attempt.phase + before.attempt.generation <
      after.attempt.phase + after.attempt.generation := by
    by_contra failure
    have samePhase : before.attempt.phase = after.attempt.phase := by omega
    have sameGeneration : before.attempt.generation = after.attempt.generation := by omega
    exact different (congrArg₂ CommitAttemptId.mk samePhase sameGeneration)
  have reserve : graph.order.eventCount + Fintype.card Player -
      (after.attempt.phase + after.attempt.generation) + 1 ≤
    graph.order.eventCount + Fintype.card Player -
      (before.attempt.phase + before.attempt.generation) := by omega
  have scaled := Nat.mul_le_mul_right (graph.order.eventCount + 1) reserve
  rw [Nat.add_mul, Nat.one_mul] at scaled
  have remaining : after.current.native.config.remaining ≤ graph.order.eventCount := Nat.sub_le _ _
  unfold workRemaining
  omega

omit [DecidableEq Player] in
theorem work_decreases_of_completion (before after : PhaseRuntimeState graph)
    (same : before.attempt = after.attempt)
    (completed : before.current.native.config.cut.completed ⊆
      after.current.native.config.cut.completed)
    (event : graph.EventId) (fresh : event ∉ before.current.native.config.cut.completed)
    (resolved : event ∈ after.current.native.config.cut.completed) :
    workRemaining after < workRemaining before := by
  have proper : before.current.native.config.cut.completed ⊂
      after.current.native.config.cut.completed :=
    Finset.ssubset_iff_subset_ne.mpr ⟨completed, by
      intro equality
      exact fresh (equality ▸ resolved)⟩
  have card := Finset.card_lt_card proper
  have bound : after.current.native.config.cut.completed.card ≤ graph.order.eventCount := by
    simpa using Finset.card_le_card (Finset.subset_univ
      after.current.native.config.cut.completed)
  unfold workRemaining
  rw [same]
  unfold EventGraph.Config.remaining
  omega

/-- A due expiry of a real owner request consumes semantic work even when it
retires the current namespace and restores the source checkpoint immediately. -/
theorem expiry_work_decreases (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {inputs : graph.Inputs} (before after : PhaseRuntimeState graph)
    (valid : before.Invariant inputs) (ordered : before.Ordered) (budget : before.SeedBudget)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.SeedRequest owner coordinate)
    (due : runtime.deadline coordinate.event ≤ before.current.native.clock -
      (before.current.native.activatedAt coordinate.event).getD before.current.native.clock)
    (reached : after ∈ (before.environment runtime (.expire coordinate.event)).support) :
    workRemaining after < workRemaining before := by
  have progress := (phaseApplication_namespace_progress runtime leaks).environment
    before (.expire coordinate.event) after reached ordered
  have afterBudget := (phaseApplication_seedBudget runtime leaks).environment
    before (.expire coordinate.event) after budget reached
  by_cases same : before.attempt = after.attempt
  · have native := before.environment_progress_of_same_namespace runtime after _ valid ordered
      reached same
    have resolved := before.expire_resolves_of_request runtime after valid ordered
      request due reached
    refine work_decreases_of_completion before after same native.completed coordinate.event
      request.2.2.1.1 ?_
    rcases resolved with retired | completed
    · exact False.elim (retired (request.1.trans same))
    · exact completed
  · have phaseBound : after.attempt.phase ≤ graph.order.eventCount :=
      PhaseRuntimeState.phaseLow_le_count after.phases
    exact work_decreases_of_namespace before after progress.2 progress.1 phaseBound
      afterBudget.generation_le_card same

end Vegas.EventGraphRuntime.ReservedEpoch
