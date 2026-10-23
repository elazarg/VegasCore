/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseServiceProgress

/-! # A physically resolved event never regains its original request -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace CommitAttemptEvent

/-- Resolution is permanent at the physical coordinate: either its namespace
has retired, or its current semantic cell has completed. -/
def Resolved (coordinate : CommitAttemptEvent graph) (state : PhaseRuntimeState graph) : Prop :=
  coordinate.attempt.generation < state.attempt.generation ∨
    coordinate.attempt.phase < state.attempt.phase ∨
      (coordinate.attempt = state.attempt ∧
        coordinate.event ∈ state.current.native.config.cut.completed)

omit [DecidableEq Player] in
private theorem namespace_eq_of_no_strict (before after : CommitAttemptId)
    (progress : before.generation ≤ after.generation ∧ before.phase ≤ after.phase)
    (generation : ¬ before.generation < after.generation)
    (phase : ¬ before.phase < after.phase) : before = after := by
  have generations : before.generation = after.generation := by omega
  have phases : before.phase = after.phase := by omega
  cases before
  cases after
  simp_all

omit [DecidableEq Player] in
/-- The usual completion-or-retirement disjunction is physical resolution when
an actual transition advances both namespace coordinates monotonically. -/
theorem Resolved.of_step (coordinate : CommitAttemptEvent graph)
    (before after : PhaseRuntimeState graph) (current : coordinate.attempt = before.attempt)
    (progress : before.attempt.generation ≤ after.attempt.generation ∧
      before.attempt.phase ≤ after.attempt.phase)
    (resolved : coordinate.attempt ≠ after.attempt ∨
      coordinate.event ∈ after.current.native.config.cut.completed) :
    coordinate.Resolved after := by
  by_cases generation : before.attempt.generation < after.attempt.generation
  · exact Or.inl (by simpa only [current] using generation)
  · by_cases phase : before.attempt.phase < after.attempt.phase
    · exact Or.inr (Or.inl (by simpa only [current] using phase))
    · have same := namespace_eq_of_no_strict before.attempt after.attempt progress generation phase
      have atCurrent := current.trans same
      refine Or.inr (Or.inr ⟨atCurrent, ?_⟩)
      exact resolved.resolve_left (fun different => different atCurrent)

omit [DecidableEq Player] in
private theorem Resolved.transport (coordinate : CommitAttemptEvent graph)
    (before after : PhaseRuntimeState graph) (resolved : coordinate.Resolved before)
    (progress : before.attempt.generation ≤ after.attempt.generation ∧
      before.attempt.phase ≤ after.attempt.phase)
    (complete : before.attempt = after.attempt →
      before.current.native.config.cut.completed ⊆ after.current.native.config.cut.completed) :
    coordinate.Resolved after := by
  rcases resolved with retiredGeneration | retiredPhase | ⟨same, completed⟩
  · exact Or.inl (retiredGeneration.trans_le progress.1)
  · exact Or.inr (Or.inl (retiredPhase.trans_le progress.2))
  · exact Resolved.of_step coordinate before after same progress
      (by
        by_cases generation : before.attempt.generation < after.attempt.generation
        · exact Or.inl (fun equal => by
            have := congrArg CommitAttemptId.generation (same.symm.trans equal)
            omega)
        · by_cases phase : before.attempt.phase < after.attempt.phase
          · exact Or.inl (fun equal => by
              have := congrArg CommitAttemptId.phase (same.symm.trans equal)
              omega)
          · have equal := namespace_eq_of_no_strict before.attempt after.attempt progress
              generation phase
            exact Or.inr (complete equal completed))

omit [DecidableEq Player] in
theorem Resolved.not_request (coordinate : CommitAttemptEvent graph)
    (state : PhaseRuntimeState graph) (resolved : coordinate.Resolved state) (owner : Player) :
    ¬ state.SeedRequest owner coordinate := by
  intro request
  rcases resolved with generation | phase | ⟨_, completed⟩
  · rw [request.1] at generation
    exact Nat.lt_irrefl _ generation
  · rw [request.1] at phase
    exact Nat.lt_irrefl _ phase
  · exact request.2.2.1.1 completed

end CommitAttemptEvent

/-- Actual phase operations preserve physical resolution, including arbitrary
private responses and subsequent rollback of later semantic phases. -/
theorem phaseApplication_resolution (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (coordinate : CommitAttemptEvent graph) :
    (phaseApplication runtime leaks).StepRelation (fun before after => ∀ inputs,
      before.Invariant inputs → before.Ordered → coordinate.Resolved before →
        coordinate.Resolved after) where
  refl _ _ _ _ old := old
  submit state who material _inputs valid ordered old := by
    apply CommitAttemptEvent.Resolved.transport coordinate state _ old
      ((phaseApplication_namespace_progress runtime leaks).submit state who material ordered)
    intro _same
    exact (state.submit_progress who material valid.active).completed
  handle state message next accepted _inputs valid ordered old := by
    apply CommitAttemptEvent.Resolved.transport coordinate state next old
      ((phaseApplication_namespace_progress runtime leaks).handle state message next accepted
        ordered)
    intro same
    exact (state.handle_progress_of_same_namespace runtime next message valid ordered accepted
      same).completed
  environment state command next reached _inputs valid ordered old := by
    apply CommitAttemptEvent.Resolved.transport coordinate state next old
      ((phaseApplication_namespace_progress runtime leaks).environment state command next reached
        ordered)
    intro same
    exact (state.environment_progress_of_same_namespace runtime next command valid ordered reached
      same).completed
end Vegas.EventGraphRuntime
