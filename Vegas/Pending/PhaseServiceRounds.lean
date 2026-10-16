/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceProgress
import Vegas.Pending.PhaseNamespace
import Interaction.ReactivePolicyInvariant

/-! # Native service progress across surviving physical attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem same_attempt_service_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (inputs : graph.Inputs) (initial : PhaseRuntimeState graph) :
    (phaseApplication runtime leaks).Invariant (fun state => state.Invariant inputs ∧
      state.Ordered ∧ initial.attempt.generation ≤ state.attempt.generation ∧
      initial.attempt.phase ≤ state.attempt.phase ∧
      (initial.attempt = state.attempt → ∃ ticks,
        State.ServiceProgress inputs ticks initial.current.native state.current.native)) := by
  let app := phaseApplication runtime leaks
  have advance (before after : PhaseRuntimeState graph)
      (valid : before.Invariant inputs) (nextValid : after.Invariant inputs)
      (ordered : before.Ordered) (nextOrdered : after.Ordered)
      (lowerGen : initial.attempt.generation ≤ before.attempt.generation)
      (lowerPhase : initial.attempt.phase ≤ before.attempt.phase)
      (progress : before.attempt.generation ≤ after.attempt.generation ∧
        before.attempt.phase ≤ after.attempt.phase)
      (previous : initial.attempt = before.attempt → ∃ ticks,
        State.ServiceProgress inputs ticks initial.current.native before.current.native)
      (service : before.Invariant inputs → before.Ordered → before.attempt = after.attempt →
        ∃ ticks, State.ServiceProgress inputs ticks before.current.native after.current.native) :
      after.Invariant inputs ∧ after.Ordered ∧
        initial.attempt.generation ≤ after.attempt.generation ∧
        initial.attempt.phase ≤ after.attempt.phase ∧
        (initial.attempt = after.attempt → ∃ ticks,
          State.ServiceProgress inputs ticks initial.current.native after.current.native) := by
    refine ⟨nextValid, nextOrdered, lowerGen.trans progress.1, lowerPhase.trans progress.2, ?_⟩
    intro same
    have generationEq : initial.attempt.generation = before.attempt.generation :=
      Nat.le_antisymm lowerGen (by
        rw [congrArg CommitAttemptId.generation same]
        exact progress.1)
    have phaseEq : initial.attempt.phase = before.attempt.phase :=
      Nat.le_antisymm lowerPhase (by
        rw [congrArg CommitAttemptId.phase same]
        exact progress.2)
    have middle : initial.attempt = before.attempt :=
      congrArg₂ CommitAttemptId.mk phaseEq generationEq
    obtain ⟨firstTicks, first⟩ := previous middle
    obtain ⟨lastTicks, last⟩ := service valid ordered (middle.symm.trans same)
    exact ⟨firstTicks + lastTicks, first.trans last⟩
  refine ⟨?_, ?_, ?_⟩
  · intro state who material valid
    exact advance state (app.submit state who material) valid.1
      ((phaseApplication_invariant runtime leaks inputs).submit state who material valid.1)
      valid.2.1 ((phaseApplication_seedOrder runtime leaks).submit state who material valid.2.1)
      valid.2.2.1 valid.2.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).submit state who material valid.2.1)
      valid.2.2.2.2 (fun native ordered same =>
        (phaseApplication_serviceProgress runtime leaks).submit state who material inputs
          native ordered same)
  · intro state message next valid accepted
    exact advance state next valid.1
      ((phaseApplication_invariant runtime leaks inputs).handle state message next valid.1 accepted)
      valid.2.1
      ((phaseApplication_seedOrder runtime leaks).handle state message next valid.2.1 accepted)
      valid.2.2.1 valid.2.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).handle state message next accepted
        valid.2.1)
      valid.2.2.2.2 (fun native ordered same =>
        (phaseApplication_serviceProgress runtime leaks).handle state message next accepted inputs
          native ordered same)
  · intro state command next valid reached
    exact advance state next valid.1
      ((phaseApplication_invariant runtime leaks inputs).environment state command next valid.1
        reached)
      valid.2.1
      ((phaseApplication_seedOrder runtime leaks).environment state command next valid.2.1 reached)
      valid.2.2.1 valid.2.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).environment state command next reached
        valid.2.1)
      valid.2.2.2.2 (fun native ordered same =>
        (phaseApplication_serviceProgress runtime leaks).environment state command next reached
          inputs native ordered same)

/-- Equal endpoint namespaces exclude intermediate retries. Arbitrary actual
rounds therefore compose completion, clock and activation-stamp progress. -/
theorem phase_runRounds_serviceProgress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {inputs : graph.Inputs} (players : Player → (phaseApplication runtime leaks).Policy)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (count : Nat)
    (before after : (phaseApplication runtime leaks).Execution)
    (valid : before.application.Invariant inputs) (ordered : before.application.Ordered)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds scheduler players count
      before).support) (same : before.application.attempt = after.application.attempt) :
    ∃ ticks, State.ServiceProgress inputs ticks before.application.current.native
      after.application.current.native := by
  have result := ((same_attempt_service_invariant runtime leaks inputs
    before.application).policyInvariant (phaseApplication runtime leaks) players).runRounds
      scheduler count before after
      ⟨valid, ordered, le_rfl, le_rfl, fun _ => ⟨0, .refl valid.active⟩⟩ reached
  exact result.2.2.2.2 same

end Vegas.EventGraphRuntime
