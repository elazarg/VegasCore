/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventValueSwap
import Vegas.Pending.PhaseApplication

/-! # Existing hidden value swaps through saved and retired physical attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RecoveryState

/-- Swap hidden semantic values while retaining permanent exclusion. -/
def swap (swap : HiddenSwap graph) (state : RecoveryState graph) : RecoveryState graph :=
  ⟨state.native.swap swap, state.excluded⟩

@[simp] theorem swap_native (swap : HiddenSwap graph) (state : RecoveryState graph) :
    (state.swap swap).native = state.native.swap swap := rfl

@[simp] theorem swap_excluded (swap : HiddenSwap graph) (state : RecoveryState graph) :
    (state.swap swap).excluded = state.excluded := rfl

theorem swap_involutive (swap : HiddenSwap graph) : Function.Involutive (RecoveryState.swap swap) :=
    by
  rintro ⟨native, excluded⟩
  exact congrArg (fun native => RecoveryState.mk native excluded)
    (State.swap_involutive swap native)

end RecoveryState

namespace RetiredCommitAttempt

/-- An archive keeps its physical namespace and swaps only hidden native data. -/
def swap (swap : HiddenSwap graph) (record : RetiredCommitAttempt graph) :
    RetiredCommitAttempt graph := ⟨record.attempt, record.state.swap swap⟩

theorem swap_involutive (swap : HiddenSwap graph) :
    Function.Involutive (RetiredCommitAttempt.swap swap) := by
  rintro ⟨attempt, state⟩
  exact congrArg (RetiredCommitAttempt.mk attempt) (State.swap_involutive swap state)

end RetiredCommitAttempt

namespace PhaseRuntimeState

/-- The same existing swap acts on both semantic checkpoints and every archive. -/
def swap (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) : PhaseRuntimeState graph :=
  { state with
    entry := state.entry.swap swap
    current := state.current.swap swap
    retired := state.retired.map (RetiredCommitAttempt.swap swap) }

@[simp] theorem swap_phases (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) :
    (state.swap swap).phases = state.phases := rfl

@[simp] theorem swap_entry (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) :
    (state.swap swap).entry = state.entry.swap swap := rfl

@[simp] theorem swap_current (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) :
    (state.swap swap).current = state.current.swap swap := rfl

@[simp] theorem swap_retired (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) :
    (state.swap swap).retired = state.retired.map (RetiredCommitAttempt.swap swap) := rfl

@[simp] theorem swap_generation (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) :
    (state.swap swap).generation = state.generation := rfl

@[simp] theorem swap_attempt (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) :
    (state.swap swap).attempt = state.attempt := rfl

theorem swap_involutive (swap : HiddenSwap graph) :
    Function.Involutive (PhaseRuntimeState.swap swap) := by
  rintro ⟨phases, generation, entry, current, retired⟩
  change (⟨phases, generation, (entry.swap swap).swap swap, (current.swap swap).swap swap,
    (retired.map (RetiredCommitAttempt.swap swap)).map (RetiredCommitAttempt.swap swap)⟩ :
      PhaseRuntimeState graph) = _
  rw [RecoveryState.swap_involutive swap entry, RecoveryState.swap_involutive swap current]
  congr 1
  rw [List.map_map]
  exact List.map_id'' (fun record => RetiredCommitAttempt.swap_involutive swap record) retired

@[simp] theorem swap_publicView (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) :
    (state.swap swap).publicView = state.publicView := by
  simp only [publicView, PhaseRuntimeState.swap, RecoveryState.swap, State.swap_publicView,
    List.map_map, RetiredCommitAttempt.swap, Function.comp_def, attempt]

/-- Restore keeps the same global clock and catalogue while swapping the saved
semantic checkpoint; ready-time reconstruction reads only the unchanged cut. -/
theorem restore_swap (swap : HiddenSwap graph) (entry current : RecoveryState graph) :
    restore (entry.swap swap) (current.swap swap) = (restore entry current).swap swap := rfl

end PhaseRuntimeState

namespace State

/-- Automatic failure commutes with every failure-preserving native value swap.
Publication actions and outputs are fixed by the existing public-swap laws. -/
theorem completeFailure_swap (swap : HiddenSwap graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (expiry : swap.values.ExpiryFixed event) :
    (state.swap swap).completeFailure event ready = (state.completeFailure event ready).swap swap :=
    by
  cases node : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      simp only [completeFailure, node, State.swap_complete,
        swap.values.action_binding event owner payload outputEq,
        expiry owner payload outputEq, cast_cast, cast_eq]
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [completeFailure, node, State.swap_complete,
        swap.values.action_publication event payload outputEq,
        swap.values.value_public (.inr event)
          (show (graph.outputLayout event).IsPublic by rw [outputEq]; trivial)]
      rfl
  | sample payload law outputEq codeEq => simp only [completeFailure, node]

end State

namespace RecoveryState

theorem completeAutomatic_swap (swap : HiddenSwap graph) (state : RecoveryState graph)
    (event : graph.EventId) (eligible : state.AutomaticReady event)
    (expiry : swap.values.ExpiryFixed event) :
    (state.swap swap).completeAutomatic event eligible =
      (state.completeAutomatic event eligible).swap swap := by
  exact congrArg (fun native => RecoveryState.mk native state.excluded)
    (state.native.completeFailure_swap swap event eligible.1 expiry)

end RecoveryState

namespace RuntimePhase

variable [DecidableEq Player]

/-- Deterministic phase-local drain makes the same selections after the swap:
its choice predicate inspects only event addresses, readiness and exclusion. -/
theorem drainFuel_swap (swap : HiddenSwap graph) (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) (expiry : ∀ event, swap.values.ExpiryFixed event) :
    phase.drainFuel fuel (state.swap swap) = (phase.drainFuel fuel state).swap swap := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      have readyEq : (state.swap swap).AutomaticReady = state.AutomaticReady := rfl
      simp only [drainFuel, readyEq]
      split
      · rw [RecoveryState.completeAutomatic_swap swap _ _ _ (expiry _)]
        exact ih _
      · rfl

/-- All automatic work stays in the same physical phase under the swap. -/
theorem drain_swap (swap : HiddenSwap graph) (phase : RuntimePhase graph)
    (state : RecoveryState graph) (expiry : ∀ event, swap.values.ExpiryFixed event) :
    phase.drain (state.swap swap) = (phase.drain state).swap swap :=
  phase.drainFuel_swap swap _ state expiry

omit [DecidableEq Player] in
@[simp] theorem finished_swap (swap : HiddenSwap graph) (phase : RuntimePhase graph)
    (state : RecoveryState graph) : phase.Finished (state.swap swap) ↔ phase.Finished state :=
  Iff.rfl

end RuntimePhase

namespace PhaseRuntimeState

variable [DecidableEq Player]

/-- Clean advancement, exhaustion and retries choose the same branch and save
or restore the swapped semantic data, preserving physical namespaces and archives. -/
theorem settle_swap (swap : HiddenSwap graph) (phases : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    settle phases generation (entry.swap swap) (current.swap swap)
      (retired.map (RetiredCommitAttempt.swap swap)) =
      (settle phases generation entry current retired).swap swap := by
  classical
  induction phases generalizing generation entry current retired with
  | nil => rfl
  | cons phase remaining ih =>
      simp only [settle, phase.drain_swap swap current expiry, RuntimePhase.finished_swap,
        RecoveryState.swap_excluded]
      by_cases finished : phase.Finished (phase.drain current)
      · simp only [finished, ↓reduceIte]
        by_cases missed : phase.kind = .commitment ∧
            (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty
        · simp only [missed, and_self, ↓reduceIte]
          rw [restore_swap, phase.drain_swap swap _ expiry]
          by_cases survives : (phase.owners \ (phase.drain current).excluded).Nonempty
          · simp only [survives, ↓reduceIte, PhaseRuntimeState.swap, List.map_append,
              List.map_cons, List.map_nil, RetiredCommitAttempt.swap, RecoveryState.swap_native]
          · simp only [survives, ↓reduceIte]
            have later := ih generation (phase.drain (restore entry (phase.drain current)))
              (phase.drain (restore entry (phase.drain current)))
              (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩])
            rw [List.map_append, List.map_cons, List.map_nil] at later
            exact later
        · simp only [missed, ↓reduceIte]
          exact ih generation (phase.drain current) (phase.drain current) retired
      · simp only [finished, ↓reduceIte]
        rfl

/-- Actual normalization retains the same phase and retry metadata under swap. -/
theorem normalize_swap (swap : HiddenSwap graph) (state : PhaseRuntimeState graph)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    (state.swap swap).normalize = state.normalize.swap swap :=
  settle_swap swap _ _ _ _ _ expiry

end PhaseRuntimeState
end Vegas.EventGraphRuntime
