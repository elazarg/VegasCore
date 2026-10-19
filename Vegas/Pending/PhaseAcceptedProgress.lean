/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearNativeProgress
import Interaction.ReactiveInvariantPrefix

/-! # Accepted handles persist throughout a surviving physical attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Same-attempt settlement only drains, and draining preserves accepted handles. -/
theorem normalize_preserves_accepted (state : PhaseRuntimeState graph) (ordered : state.Ordered)
    (same : state.attempt = state.normalize.attempt) (field : graph.Field)
    (candidate : Handle graph) (present : state.current.native.accepted field = some candidate) :
    state.normalize.current.native.accepted field = some candidate := by
  have settled := settle_of_same_namespace state.phases state.generation state.entry
    state.current state.retired ordered same
  have currentEq := congrArg PhaseRuntimeState.current settled
  change State.accepted
    (settle state.phases state.generation state.entry state.current state.retired).current.native
      field = some candidate
  rw [currentEq]
  cases phases : state.phases with
  | nil => exact present
  | cons phase rest =>
      change (phase.drain state.current).native.accepted field = some candidate
      rw [(phase.drain_tables state.current).1]
      exact present

/-- Raw submissions, handlers and environment commands retain each accepted
handle whenever the physical attempt is unchanged. -/
theorem accepted_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      before.Ordered → before.attempt = after.attempt → ∀ field candidate,
        before.current.native.accepted field = some candidate →
          after.current.native.accepted field = some candidate) where
  refl _state _ _ _ _ present := present
  submit state who submission _ _ field candidate present := by
    change (submitStep (submission.call.register state.current.native who) who
      submission.call.packet).accepted field = some candidate
    rw [submitStep_accepted, Submission.register_accepted]
    exact present
  handle state message next accepted ordered same field candidate present := by
    change state.handle runtime message = some next at accepted
    unfold handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact normalize_preserves_accepted
        ({ state with current :=
          state.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph) ordered same field candidate
            (handle_preserves_accepted runtime _ native _ handled field candidate present)
    · cases accepted
  environment state command next reached ordered same field candidate present := by
    change next ∈ (state.environment runtime command).support at reached
    unfold environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      apply normalize_preserves_accepted
        ({ state with current := state.current.environmentResult command native } :
          PhaseRuntimeState graph) ordered same field candidate
      change native.accepted field = some candidate
      rw [(environmentStep_tables runtime _ native command supported).1]
      exact present
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact present

end PhaseRuntimeState

private theorem same_attempt_accepted_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (initial : PhaseRuntimeState graph) :
    (phaseApplication runtime leaks).Invariant (fun state => state.Ordered ∧
      initial.attempt.generation ≤ state.attempt.generation ∧
      initial.attempt.phase ≤ state.attempt.phase ∧
      (initial.attempt = state.attempt → ∀ field candidate,
        initial.current.native.accepted field = some candidate →
          state.current.native.accepted field = some candidate)) := by
  let app := phaseApplication runtime leaks
  have advance (before after : PhaseRuntimeState graph)
      (ordered : before.Ordered) (nextOrdered : after.Ordered)
      (lowerGen : initial.attempt.generation ≤ before.attempt.generation)
      (lowerPhase : initial.attempt.phase ≤ before.attempt.phase)
      (progress : before.attempt.generation ≤ after.attempt.generation ∧
        before.attempt.phase ≤ after.attempt.phase)
      (previous : initial.attempt = before.attempt → ∀ field candidate,
        initial.current.native.accepted field = some candidate →
          before.current.native.accepted field = some candidate)
      (extension : before.Ordered → before.attempt = after.attempt → ∀ field candidate,
        before.current.native.accepted field = some candidate →
          after.current.native.accepted field = some candidate) :
      after.Ordered ∧ initial.attempt.generation ≤ after.attempt.generation ∧
        initial.attempt.phase ≤ after.attempt.phase ∧
        (initial.attempt = after.attempt → ∀ field candidate,
          initial.current.native.accepted field = some candidate →
            after.current.native.accepted field = some candidate) := by
    refine ⟨nextOrdered, lowerGen.trans progress.1, lowerPhase.trans progress.2, ?_⟩
    intro same field candidate present
    have middle : initial.attempt = before.attempt := by
      have gen := congrArg CommitAttemptId.generation same
      have phase := congrArg CommitAttemptId.phase same
      cases original : initial.attempt with
      | mk firstPhase firstGeneration =>
          cases current : before.attempt with
          | mk nextPhase nextGeneration =>
              simp only [original, current] at lowerGen lowerPhase progress gen phase ⊢
              congr 1 <;> omega
    exact extension ordered (middle.symm.trans same) field candidate
      (previous middle field candidate present)
  refine ⟨?_, ?_, ?_⟩
  · intro state who material valid
    exact advance state (app.submit state who material) valid.1
      ((phaseApplication_seedOrder runtime leaks).submit state who material valid.1)
      valid.2.1 valid.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).submit state who material valid.1)
      valid.2.2.2 ((PhaseRuntimeState.accepted_progress runtime leaks).submit state who material)
  · intro state message next valid accepted
    exact advance state next valid.1
      ((phaseApplication_seedOrder runtime leaks).handle state message next valid.1 accepted)
      valid.2.1 valid.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).handle state message next accepted
        valid.1)
      valid.2.2.2 ((PhaseRuntimeState.accepted_progress runtime leaks).handle state message next
        accepted)
  · intro state command next valid reached
    exact advance state next valid.1
      ((phaseApplication_seedOrder runtime leaks).environment state command next valid.1 reached)
      valid.2.1 valid.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).environment state command next reached
        valid.1)
      valid.2.2.2 ((PhaseRuntimeState.accepted_progress runtime leaks).environment state command
        next reached)

/-- An actual trace prefix keeps each accepted handle in its original
physical attempt. Namespace monotonicity rules out an intermediate retry. -/
theorem phase_prefix_accepted (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (final : (menu.protocol initial horizon scheduler).Trace (some after))
    (kept : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior final)
    (ordered : before.execution.application.Ordered)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (field : graph.Field) (candidate : Handle graph)
    (present : before.execution.application.current.native.accepted field = some candidate) :
    after.execution.application.current.native.accepted field = some candidate := by
  have valid := (same_attempt_accepted_invariant runtime leaks
    before.execution.application).tracePrefix menu initial horizon scheduler before after prior
      final kept ⟨ordered, Nat.le_refl _, Nat.le_refl _, fun _ _ _ present => present⟩
  exact valid.2.2.2 same field candidate present

/-- Supported physical rounds keep all accepted handles if their endpoint
attempt agrees with the original attempt; intermediate resets are excluded by
namespace monotonicity, rather than by an extra no-reset assumption. -/
theorem phase_runRounds_accepted (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (players : Player → (phaseApplication runtime leaks).Policy)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (count : Nat)
    (before after : (phaseApplication runtime leaks).Execution)
    (ordered : before.application.Ordered)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds scheduler players count
      before).support) (same : before.application.attempt = after.application.attempt)
    (field : graph.Field) (candidate : Handle graph)
    (present : before.application.current.native.accepted field = some candidate) :
    after.application.current.native.accepted field = some candidate := by
  have valid := ((same_attempt_accepted_invariant runtime leaks before.application).policyInvariant
    (phaseApplication runtime leaks) players).runRounds scheduler count before after
    ⟨ordered, Nat.le_refl _, Nat.le_refl _, fun _ _ _ present => present⟩ reached
  exact valid.2.2.2 same field candidate present

end Vegas.EventGraphRuntime
