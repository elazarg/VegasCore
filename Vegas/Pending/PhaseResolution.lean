/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNamespace
import Vegas.Pending.EventProgress

/-! # Physical resolution survives immediate phase normalization

A physical deadline reply completes the old native event before normalization.
Normalization either preserves that completion or retires its physical
namespace; a retry need not preserve the static event's semantic completion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RuntimePhase

theorem drainFuel_completed (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) :
    state.native.config.cut.completed ⊆
      (phase.drainFuel fuel state).native.config.cut.completed := by
  induction fuel generalizing state with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        have eligible := (Classical.choose_spec pending).2
        obtain ⟨action, moved⟩ := state.completeAutomatic_step _ eligible
        exact (State.completed_subset_of_mem_step _ _ eligible.1 action _ moved).trans (ih _)
      · exact Finset.Subset.refl _

theorem drain_completed (phase : RuntimePhase graph) (state : RecoveryState graph) :
    state.native.config.cut.completed ⊆ (phase.drain state).native.config.cut.completed :=
  drainFuel_completed phase _ state

end RuntimePhase

namespace PhaseRuntimeState

omit [DecidableEq Player] in
theorem phaseLow_lt_tail (phase : RuntimePhase graph)
    (remaining : List (RuntimePhase graph))
    (ordered : (phase :: remaining).IsChain (fun before after => before.high = after.low)) :
    phase.low < phaseLow remaining := by
  cases remaining with
  | nil => exact phase.nonempty.trans_le phase.bounded
  | cons next later =>
      exact phase.nonempty.trans_eq (List.isChain_cons_cons.mp ordered).1

/-- If normalization retains the current physical namespace, it only performs
phase-local automatic completions; it has not restored an earlier checkpoint. -/
theorem settle_current_of_same_namespace (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (ordered : phases.IsChain (fun before after => before.high = after.low))
    (same : (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph).attempt =
      (settle phases generation entry current retired).attempt) :
    (settle phases generation entry current retired).current =
      phases.head?.elim current (fun phase => phase.drain current) := by
  classical
  cases phases with
  | nil => rfl
  | cons phase remaining =>
      have later (saved active : RecoveryState graph)
          (archive : List (RetiredCommitAttempt graph)) :
          (⟨phase :: remaining, generation, entry, current, retired⟩ :
            PhaseRuntimeState graph).attempt ≠
              (settle remaining generation saved active archive).attempt := by
        intro equal
        have lower := phaseLow_lt_tail phase remaining ordered
        have progress := (settle_namespace remaining generation saved active archive ordered.tail).2
        have phaseEq := congrArg CommitAttemptId.phase equal
        change phase.low =
          (settle remaining generation saved active archive).attempt.phase at phaseEq
        omega
      by_cases finished : phase.Finished (phase.drain current)
      · by_cases missed : phase.kind = .commitment ∧
            (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty
        · by_cases survivors : (phase.owners \ (phase.drain current).excluded).Nonempty
          · rw [settle_retry phase remaining generation entry current retired finished
              missed.1 missed.2 survivors] at same
            have generationEq := congrArg CommitAttemptId.generation same
            change generation = generation + 1 at generationEq
            omega
          · rw [settle_exhausted phase remaining generation entry current retired finished
              missed.1 missed.2 survivors] at same
            exact False.elim (later _ _ _ same)
        · rw [settle_clean phase remaining generation entry current retired finished missed] at same
          exact False.elim (later _ _ _ same)
      · simp only [settle, finished, ite_false, List.head?_cons, Option.elim_some]

/-- Every raw completed event either remains complete or belongs to a namespace
that normalization has retired. No promise is made about retrying source cells. -/
theorem settle_resolves (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (ordered : phases.IsChain (fun before after => before.high = after.low))
    (event : graph.EventId) (completed : event ∈ current.native.config.cut.completed) :
    (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph).attempt ≠
        (settle phases generation entry current retired).attempt ∨
      event ∈
        (settle phases generation entry current retired).current.native.config.cut.completed := by
  by_cases same :
      (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph).attempt =
      (settle phases generation entry current retired).attempt
  · right
    rw [settle_current_of_same_namespace phases generation entry current retired ordered same]
    cases phases with
    | nil => exact completed
    | cons phase remaining => exact phase.drain_completed current completed
  · exact Or.inl same

/-- An actual due expiry resolves its current physical address. The reply may
close a failed phase and immediately restore semantic cells for a fresh retry. -/
theorem expire_resolves_of_request (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) {inputs : graph.Inputs}
    (valid : state.Invariant inputs) (ordered : state.Ordered) {owner : Player}
    {coordinate : CommitAttemptEvent graph} (request : state.SeedRequest owner coordinate)
    (due : runtime.deadline coordinate.event ≤ state.current.native.clock -
      (state.current.native.activatedAt coordinate.event).getD state.current.native.clock)
    (reached : next ∈ (state.environment runtime (.expire coordinate.event)).support) :
    coordinate.attempt ≠ next.attempt ∨
      coordinate.event ∈ next.current.native.config.cut.completed := by
  obtain ⟨sameAttempt, ⟨phase, head, inside⟩, ready, acting, _⟩ := request
  change state.phases.head? = some phase at head
  have allowed : state.commandAllowed (.expire coordinate.event) = true := by
    simp only [commandAllowed, head, Option.any_some, inside, decide_true]
  unfold environment at reached
  rw [ite_eq_left allowed, PMF.support_map] at reached
  obtain ⟨native, nativeReached, rfl⟩ := reached
  have activatedSome := (valid.active.activated_iff coordinate.event).mpr
    ⟨ready, by simp only [acting, Option.isSome_some]⟩
  cases activated : state.current.native.activatedAt coordinate.event with
  | none => simp only [activated, Option.isSome_none, Bool.false_eq_true] at activatedSome
  | some entered =>
      have deadline : runtime.deadline coordinate.event ≤ state.current.native.clock - entered := by
        simpa only [activated, Option.getD_some] using due
      have completed := environmentStep_expire_complete runtime state.current.native native
        coordinate.event ready (by simp only [acting, Option.isSome_some]) entered activated
          deadline nativeReached
      rw [sameAttempt]
      exact settle_resolves state.phases state.generation state.entry
        (state.current.environmentResult (.expire coordinate.event) native) state.retired ordered
          coordinate.event completed

end PhaseRuntimeState
end Vegas.EventGraphRuntime
