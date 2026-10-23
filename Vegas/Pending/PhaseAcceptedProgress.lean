/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseClearNativeProgress
import Interaction.ReactiveInvariantPrefix
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveRounds
import Vegas.Pending.PhaseNamespace
import Vegas.Pending.PhaseResolution
import Vegas.Pending.ReactiveSignedCommitments

/-! # Accepted handles persist throughout a surviving physical attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Every handle accepted at the saved checkpoint is still accepted in the
live state. A retry restores the saved associations before draining again. -/
def AcceptedCheckpoint (state : PhaseRuntimeState graph) : Prop :=
  ∀ field candidate, state.entry.native.accepted field = some candidate →
    state.current.native.accepted field = some candidate

/-- Automatic settlement retains saved accepted handles, including when a
dirty phase restores and immediately exhausts several subsequent phases. -/
theorem settle_acceptedCheckpoint (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (saved : ∀ field candidate, entry.native.accepted field = some candidate →
      current.native.accepted field = some candidate) :
    (settle phases generation entry current retired).AcceptedCheckpoint := by
  induction phases generalizing generation entry current retired with
  | nil => exact saved
  | cons phase rest ih =>
      have drained : ∀ field candidate, entry.native.accepted field = some candidate →
          (phase.drain current).native.accepted field = some candidate := by
        intro field candidate present
        rw [(phase.drain_tables current).1]
        exact saved field candidate present
      simp only [settle]
      split
      · split
        · split
          · intro field candidate present
            change (phase.drain (restore entry (phase.drain current))).native.accepted field =
              some candidate
            rw [(phase.drain_tables _).1]
            exact present
          · exact ih _ _ _ _ (fun _ _ present => present)
        · exact ih _ _ _ _ (fun _ _ present => present)
      · exact drained

theorem initial_acceptedCheckpoint (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).AcceptedCheckpoint :=
  settle_acceptedCheckpoint _ _ _ _ _ (fun _ _ present => present)

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

/-- Submitting, including and servicing packets preserve every accepted
association already in the saved checkpoint. -/
theorem phaseApplication_acceptedCheckpoint (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.AcceptedCheckpoint where
  submit state who material valid := by
    intro field candidate present
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).accepted field = some candidate
    rw [submitStep_accepted, Submission.register_accepted]
    exact valid field candidate present
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_acceptedCheckpoint
      intro field candidate present
      exact handle_preserves_accepted runtime _ native _ handled field candidate
        (valid field candidate present)
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      apply PhaseRuntimeState.settle_acceptedCheckpoint
      intro field candidate present
      change native.accepted field = some candidate
      rw [(environmentStep_tables runtime _ native command supported).1]
      exact valid field candidate present
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid

/-- Actual initialized traces retain their saved accepted handles in the
current physical state, without requiring a source execution witness. -/
theorem phaseAcceptedCheckpoint_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.AcceptedCheckpoint :=
  (phaseApplication_acceptedCheckpoint runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_acceptedCheckpoint plan draw) trace

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
