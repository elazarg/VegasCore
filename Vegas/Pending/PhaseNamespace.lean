/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication

/-! # Seed namespaces advance through actual phase normalization

Phase completion consumes a suffix of the compiled phase list. Retry keeps the
current phase and increments the permanent generation. Consequently a retired
attempt namespace cannot become current again along an ordered execution.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

def Ordered (state : PhaseRuntimeState graph) : Prop :=
  state.phases.IsChain (fun before after => before.high = after.low)

def phaseLow (phases : List (RuntimePhase graph)) : Nat :=
  (phases.head?.map RuntimePhase.low).getD graph.order.eventCount

omit [DecidableEq Player] in
theorem phaseLow_le_count (phases : List (RuntimePhase graph)) :
    phaseLow phases ≤ graph.order.eventCount := by
  cases phases with
  | nil => exact Nat.le_refl _
  | cons phase remaining =>
      exact phase.nonempty.le.trans phase.bounded

omit [DecidableEq Player] in
private theorem phaseLow_tail (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (ordered : (phase :: remaining).IsChain (fun before after => before.high = after.low)) :
    phaseLow (phase :: remaining) ≤ phaseLow remaining := by
  cases remaining with
  | nil => exact phase.nonempty.le.trans phase.bounded
  | cons next rest =>
      have adjacent := (List.isChain_cons_cons.mp ordered).1
      exact phase.nonempty.le.trans_eq adjacent

omit [DecidableEq Player] in
theorem phaseLow_suffix {phases remaining : List (RuntimePhase graph)}
    (ordered : phases.IsChain (fun before after => before.high = after.low))
    (suffix : remaining <:+ phases) : phaseLow phases ≤ phaseLow remaining := by
  induction phases with
  | nil =>
      have empty : remaining = [] := List.suffix_nil.mp suffix
      subst remaining
      exact Nat.le_refl _
  | cons phase rest ih =>
      rcases List.suffix_cons_iff.mp suffix with same | later
      · subst remaining
        exact Nat.le_refl _
      · exact (phaseLow_tail phase rest ordered).trans (ih ordered.tail later)

theorem settle_ordered (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (ordered : phases.IsChain (fun before after => before.high = after.low)) :
    (settle phases generation entry current retired).Ordered :=
  ordered.suffix (settle_suffix _ _ _ _ _)

/-- Both parts of the physical namespace are monotone. This is independent of
which source outputs are rolled back inside the active phase. -/
theorem settle_namespace (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (ordered : phases.IsChain (fun before after => before.high = after.low)) :
    generation ≤ (settle phases generation entry current retired).attempt.generation ∧
      phaseLow phases ≤ (settle phases generation entry current retired).attempt.phase :=
  ⟨settle_generation _ _ _ _ _, phaseLow_suffix ordered (settle_suffix _ _ _ _ _)⟩

theorem initial_ordered (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).Ordered :=
  settle_ordered _ _ _ _ _ plan.adjacent

end PhaseRuntimeState

/-- Ordered phase descriptors remain ordered through the actual reset application. -/
theorem phaseApplication_seedOrder (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.Ordered where
  submit _ _ _ valid := valid
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.settle_ordered _ _ _ _ _ valid
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, reached, rfl⟩ := reached
      exact PhaseRuntimeState.settle_ordered _ _ _ _ _ valid
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Every real transition advances the namespace componentwise whenever its
current descriptor list is ordered. -/
theorem phaseApplication_namespace_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after => before.Ordered →
      before.attempt.generation ≤ after.attempt.generation ∧
        before.attempt.phase ≤ after.attempt.phase) where
  refl _ _ := ⟨Nat.le_refl _, Nat.le_refl _⟩
  submit _ _ _ _ := ⟨Nat.le_refl _, Nat.le_refl _⟩
  handle state message next accepted ordered := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.settle_namespace _ _ _ _ _ ordered
    · cases accepted
  environment state command next reached ordered := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, reached, rfl⟩ := reached
      exact PhaseRuntimeState.settle_namespace _ _ _ _ _ ordered
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end Vegas.EventGraphRuntime
