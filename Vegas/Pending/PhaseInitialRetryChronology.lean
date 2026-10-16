/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseArchiveOrder
import Vegas.Pending.PhaseArchivedRecall
import Mathlib.Order.Preorder.Finite

/-! # Exact retry namespaces before leaving the initial phase -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every retry increments its generation and appends an archive together.
Exhausting a phase can append an additional archive without incrementing. -/
theorem settle_generation_le_retired_length (phases : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph)) (counted : generation ≤ retired.length) :
    (settle phases generation entry current retired).generation ≤
      (settle phases generation entry current retired).retired.length := by
  induction phases generalizing generation entry current retired with
  | nil => exact counted
  | cons phase remaining ih =>
      simp only [settle]
      split
      · split
        · split
          · simpa only [List.length_append, List.length_singleton] using
              Nat.add_le_add_right counted 1
          · exact ih _ _ _ _ (by
              simp only [List.length_append, List.length_singleton]
              omega)
        · exact ih _ _ _ _ counted
      · exact counted

/-- Arbitrary submissions, inclusions and environment commands retain the
bound on the number of retry increments by the number of retired attempts. -/
theorem generation_le_retired_length_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant
      (fun state => state.generation ≤ state.retired.length) where
  submit _ _ _ valid := valid
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact settle_generation_le_retired_length _ _ _ _ _ valid
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact settle_generation_le_retired_length _ _ _ _ _ valid
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- This bound is a property of every initialized runtime history, independently
of the selected player policies and scheduler. -/
theorem generation_le_retired_length_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.generation ≤ control.execution.application.retired.length := by
  apply (generation_le_retired_length_invariant runtime leaks).history _ horizon scheduler
    (fun state supported => ?_) trace
  obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact settle_generation_le_retired_length _ _ _ _ _ (Nat.le_refl 0)

/-- At static phase zero, all retired attempts are exactly the consecutive
retry generations. Their order and count follow from actual runtime history. -/
theorem initial_phase_retry_namespaces (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (initial plan)) horizon scheduler).Trace (some control))
    (atStart : control.execution.application.attempt.phase = 0) :
    control.execution.application.generation = control.execution.application.retired.length ∧
      ∀ index : Fin control.execution.application.retired.length,
        (control.execution.application.retired.get index).attempt = ⟨0, index.val⟩ := by
  let state := control.execution.application
  have ordered := retiredOrdered_history runtime leaks plan inputs horizon scheduler trace
  have before := archivesBefore_history runtime leaks plan inputs horizon scheduler trace
  have counted := generation_le_retired_length_history runtime leaks plan inputs horizon
    scheduler trace
  have phaseZero (record : RetiredCommitAttempt graph) (member : record ∈ state.retired) :
      record.attempt.phase = 0 := by
    have bounded := before record member
    rw [atStart] at bounded
    omega
  have below (index : Fin state.retired.length) :
      (state.retired.get index).attempt.generation < state.generation := by
    have earlier := ordered.2 (state.retired.get index) (List.get_mem state.retired index)
    have zero := phaseZero _ (List.get_mem state.retired index)
    simp only [CommitAttemptId.Precedes] at earlier
    change (state.retired.get index).attempt.generation < state.generation
    change (state.retired.get index).attempt.generation < state.generation ∨
      (state.retired.get index).attempt.generation = state.generation ∧
        (state.retired.get index).attempt.phase < state.attempt.phase at earlier
    change state.attempt.phase = 0 at atStart
    omega
  have increasing {first second : Fin state.retired.length} (lt : first < second) :
      (state.retired.get first).attempt.generation <
        (state.retired.get second).attempt.generation := by
    have earlier := ordered.1.rel_get_of_lt lt
    change (state.retired.get first).attempt.Precedes
      (state.retired.get second).attempt at earlier
    have firstZero := phaseZero _ (List.get_mem state.retired first)
    have secondZero := phaseZero _ (List.get_mem state.retired second)
    simp only [CommitAttemptId.Precedes] at earlier
    omega
  let generations : Fin state.retired.length → Fin state.generation :=
    fun index => ⟨(state.retired.get index).attempt.generation, below index⟩
  have strict : StrictMono generations := fun _ _ lt => increasing lt
  have lengthBound : state.retired.length ≤ state.generation := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective generations strict.injective
  have exactCount : state.generation = state.retired.length := Nat.le_antisymm counted lengthBound
  refine ⟨exactCount, ?_⟩
  let positions : Fin state.retired.length → Fin state.retired.length := fun index =>
    ⟨(state.retired.get index).attempt.generation, by simpa only [← exactCount] using below index⟩
  have strictPositions : StrictMono positions := fun _ _ lt => increasing lt
  intro index
  have generationEq := congrArg Fin.val (strictPositions.apply_eq (x := index))
  have zero := phaseZero _ (List.get_mem state.retired index)
  change (state.retired.get index).attempt.generation = index.val at generationEq
  cases address : (state.retired.get index).attempt with
  | mk phase generation =>
      simp only [address] at zero generationEq
      simp only [zero, generationEq]

end Vegas.EventGraphRuntime.PhaseRuntimeState
