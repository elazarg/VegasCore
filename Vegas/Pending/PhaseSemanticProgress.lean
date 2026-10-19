/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Pending.PhaseResolution
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveInvariantPrefix

/-! # Actual immutable semantic extensions inside one physical attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Same-namespace normalization only appends actual automatic completions. -/
theorem normalize_semantic_extension (state : PhaseRuntimeState graph) (ordered : state.Ordered)
    (same : state.attempt = state.normalize.attempt) :
    KeepsStore state.current.native state.normalize.current.native ∧
      state.current.native.config.history.IsPrefix
        state.normalize.current.native.config.history := by
  have settled := settle_of_same_namespace state.phases state.generation state.entry
    state.current state.retired ordered same
  have currentEq := congrArg PhaseRuntimeState.current settled
  change KeepsStore state.current.native
    (settle state.phases state.generation state.entry state.current state.retired).current.native ∧
    state.current.native.config.history.IsPrefix
      (State.config (settle state.phases state.generation state.entry state.current
        state.retired).current.native).history
  rw [currentEq]
  cases phases : state.phases with
  | nil => exact ⟨fun _ _ present => present, ⟨[], by simp⟩⟩
  | cons phase remaining => exact ⟨phase.drain_keepsStore _, phase.drain_history_prefix _⟩

/-- Actual preparations, inclusions and environment replies extend the semantic
store and owned completion word whenever they retain the physical attempt. -/
theorem semantic_extension (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      before.Ordered → before.attempt = after.attempt →
        KeepsStore before.current.native after.current.native ∧
          before.current.native.config.history.IsPrefix after.current.native.config.history) where
  refl _state _ _ := ⟨fun _ _ present => present, ⟨[], by simp⟩⟩
  submit state who submission _ _ := by
    have configEq : (state.submit who submission).current.native.config =
        state.current.native.config := by
      change (submitStep (submission.call.register state.current.native who) who
        submission.call.packet).config = _
      rw [submitStep_config, (submission.call.register_facts who state.current.native).1]
    constructor
    · intro field value present
      change (state.submit who submission).current.native.config.store field = _
      rw [configEq]
      exact present
    · change state.current.native.config.history.IsPrefix
        (state.submit who submission).current.native.config.history
      rw [configEq]
  handle state message next accepted ordered same := by
    change state.handle runtime message = some next at accepted
    unfold handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have normalized := normalize_semantic_extension
        ({ state with current :=
          state.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph) ordered same
      refine ⟨fun field value present => normalized.1 field value
        (handle_store_of_some runtime _ native _ handled field value present), ?_⟩
      apply List.IsPrefix.trans ?_ normalized.2
      obtain ⟨event, _named, ready, action, supported⟩ :=
        handle_config_mem_step runtime _ native _ handled
      change state.current.native.config.history.IsPrefix native.config.history
      rw [state.current.native.config.step_history _ _ _ _ supported]
      exact ⟨_, rfl⟩
    · cases accepted
  environment state command next reached ordered same := by
    change next ∈ (state.environment runtime command).support at reached
    unfold environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      have normalized := normalize_semantic_extension
        ({ state with current := state.current.environmentResult command native } :
          PhaseRuntimeState graph) ordered same
      exact ⟨fun field value present => normalized.1 field value
        (environmentStep_store_of_some runtime _ native command supported field value present),
        (environmentStep_history_prefix runtime _ native command supported).trans normalized.2⟩
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨fun _ _ present => present, ⟨[], by simp⟩⟩

end PhaseRuntimeState

/-- The actual namespace is monotone, so equal endpoint attempts exclude an
intermediate restore. This anchored invariant retains the full dependent word. -/
private theorem same_attempt_extension_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (initial : PhaseRuntimeState graph) :
    (phaseApplication runtime leaks).Invariant (fun state => state.Ordered ∧
      initial.attempt.generation ≤ state.attempt.generation ∧
      initial.attempt.phase ≤ state.attempt.phase ∧
      (initial.attempt = state.attempt → KeepsStore initial.current.native state.current.native ∧
        initial.current.native.config.history.IsPrefix state.current.native.config.history)) := by
  let app := phaseApplication runtime leaks
  have advance (before after : PhaseRuntimeState graph)
      (ordered : before.Ordered) (nextOrdered : after.Ordered)
      (lowerGen : initial.attempt.generation ≤ before.attempt.generation)
      (lowerPhase : initial.attempt.phase ≤ before.attempt.phase)
      (progress : before.attempt.generation ≤ after.attempt.generation ∧
        before.attempt.phase ≤ after.attempt.phase)
      (previous : initial.attempt = before.attempt →
        KeepsStore initial.current.native before.current.native ∧
          initial.current.native.config.history.IsPrefix
            before.current.native.config.history)
      (extension : before.Ordered → before.attempt = after.attempt →
        KeepsStore before.current.native after.current.native ∧
          before.current.native.config.history.IsPrefix after.current.native.config.history) :
      after.Ordered ∧ initial.attempt.generation ≤ after.attempt.generation ∧
        initial.attempt.phase ≤ after.attempt.phase ∧
        (initial.attempt = after.attempt →
          KeepsStore initial.current.native after.current.native ∧
            initial.current.native.config.history.IsPrefix
              after.current.native.config.history) := by
    refine ⟨nextOrdered, lowerGen.trans progress.1, lowerPhase.trans progress.2, ?_⟩
    intro same
    have middle : initial.attempt = before.attempt := by
      have gen := congrArg CommitAttemptId.generation same
      have phase := congrArg CommitAttemptId.phase same
      cases original : initial.attempt with
      | mk firstPhase firstGeneration =>
          cases current : before.attempt with
          | mk nextPhase nextGeneration =>
              simp only [original, current] at lowerGen lowerPhase progress gen phase ⊢
              congr 1 <;> omega
    obtain ⟨firstStore, firstHistory⟩ := previous middle
    obtain ⟨lastStore, lastHistory⟩ := extension ordered (middle.symm.trans same)
    exact ⟨fun field value present => lastStore field value (firstStore field value present),
      firstHistory.trans lastHistory⟩
  refine ⟨?_, ?_, ?_⟩
  · intro state who material valid
    exact advance state (app.submit state who material) valid.1
      ((phaseApplication_seedOrder runtime leaks).submit state who material valid.1)
      valid.2.1 valid.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).submit state who material valid.1)
      valid.2.2.2 ((PhaseRuntimeState.semantic_extension runtime leaks).submit state who material)
  · intro state message next valid accepted
    exact advance state next valid.1
      ((phaseApplication_seedOrder runtime leaks).handle state message next valid.1 accepted)
      valid.2.1 valid.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).handle state message next accepted
        valid.1)
      valid.2.2.2 ((PhaseRuntimeState.semantic_extension runtime leaks).handle state message next
        accepted)
  · intro state command next valid reached
    exact advance state next valid.1
      ((phaseApplication_seedOrder runtime leaks).environment state command next valid.1 reached)
      valid.2.1 valid.2.2.1
      ((phaseApplication_namespace_progress runtime leaks).environment state command next reached
        valid.1)
      valid.2.2.2 ((PhaseRuntimeState.semantic_extension runtime leaks).environment state command
        next reached)

/-- A genuine retained history prefix preserves completed semantic data whenever
both actual endpoints still belong to the same physical attempt. -/
theorem phase_prefix_semantic_extension (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (final : (menu.protocol initial horizon scheduler).Trace (some after))
    (kept : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior final)
    (ordered : before.execution.application.Ordered)
    (same : before.execution.application.attempt = after.execution.application.attempt) :
    KeepsStore before.execution.application.current.native
        after.execution.application.current.native ∧
      before.execution.application.current.native.config.history.IsPrefix
        after.execution.application.current.native.config.history := by
  have valid := (same_attempt_extension_invariant runtime leaks
    before.execution.application).tracePrefix menu initial horizon scheduler before after
      prior final kept ⟨ordered, Nat.le_refl _, Nat.le_refl _, fun _ =>
        ⟨fun _ _ present => present, ⟨[], by simp⟩⟩⟩
  exact valid.2.2.2 same

/-- Arbitrary supported physical rounds retain immutable semantic fields and
chronological effective actions when their physical attempt survives. -/
theorem phase_runRounds_semantic_extension (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (players : Player → (phaseApplication runtime leaks).Policy)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (count : Nat)
    (before after : (phaseApplication runtime leaks).Execution)
    (ordered : before.application.Ordered)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds scheduler players count
      before).support) (same : before.application.attempt = after.application.attempt) :
    KeepsStore before.application.current.native after.application.current.native ∧
      before.application.current.native.config.history.IsPrefix
        after.application.current.native.config.history := by
  have valid := ((same_attempt_extension_invariant runtime leaks before.application).policyInvariant
    (phaseApplication runtime leaks) players).runRounds scheduler count before after
    ⟨ordered, Nat.le_refl _, Nat.le_refl _, fun _ =>
      ⟨fun _ _ present => present, ⟨[], by simp⟩⟩⟩ reached
  exact valid.2.2.2 same

end Vegas.EventGraphRuntime
