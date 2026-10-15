/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearHistory
import Vegas.Pending.PhaseSemanticProgress
import Vegas.Pending.PhaseSwapAdmission

/-! # Native semantic preservation through all clear phase transitions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Native acceptance only installs a previously absent binding association;
other associations remain exact, independently of the prepared value's type. -/
theorem handle_preserves_accepted (runtime : EventGraphRuntime graph)
    (before after : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime before message = some after)
    (field : graph.Field) (candidate : Handle graph) (present : before.accepted field =
      some candidate) : after.accepted field = some candidate := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | opening event named raw =>
      rw [(handle_resolution_tables runtime before after ⟨id, .opening event named raw⟩
        (fun _ _ impossible => by cases impossible) accepted).1]
      exact present
  | commitment event named =>
      have table := (handle_commitment_tables runtime before after id event named accepted).2.1
      obtain ⟨_, _, _, _, _, _, _, _, _, vacant, _⟩ :=
        handle_commitment_conditions runtime before after id event named accepted
      rw [table]
      by_cases same : field = .inr event
      · subst field
        rw [vacant] at present
        cases present
      · rw [Function.update_of_ne same]
        exact present

/-- A clear endpoint rules out rollback, even when clean phase advancement
changes the active namespace. Actual raw native writes therefore remain in
its store, effective action word, accepted table and completed cut. -/
theorem phaseApplication_clear_nativeProgress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      after.current.excluded = ∅ →
        KeepsStore before.current.native after.current.native ∧
          before.current.native.config.history.IsPrefix after.current.native.config.history ∧
          (∀ field candidate, before.current.native.accepted field = some candidate →
            after.current.native.accepted field = some candidate) ∧
          before.current.native.config.cut.completed ⊆ after.current.native.config.cut.completed)
    where
  refl _state _ := ⟨fun _ _ present => present, ⟨[], by simp⟩, fun _ _ present => present,
    fun _ member => member⟩
  submit state who submission _ := by
    have configEq : (state.submit who submission).current.native.config =
        state.current.native.config := by
      change (submitStep (submission.call.register state.current.native who) who
        submission.call.packet).config = _
      rw [submitStep_config, (submission.call.register_facts who state.current.native).1]
    have acceptedEq : (state.submit who submission).current.native.accepted =
        state.current.native.accepted := by
      change (submitStep (submission.call.register state.current.native who) who
        submission.call.packet).accepted = _
      rw [submitStep_accepted, Submission.register_accepted]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro field value present
      change (state.submit who submission).current.native.config.store field = _
      rw [configEq]
      exact present
    · change state.current.native.config.history.IsPrefix
        (state.submit who submission).current.native.config.history
      rw [configEq]
    · intro field candidate present
      change (state.submit who submission).current.native.accepted field = some candidate
      rw [acceptedEq]
      exact present
    · change state.current.native.config.cut.completed ⊆
        (state.submit who submission).current.native.config.cut.completed
      rw [configEq]
  handle state message next accepted clear := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have same := (PhaseRuntimeState.normalize_of_clear
        ({ state with current := (state.current.inclusionResult
          message.payload.packet.call native) } :
          PhaseRuntimeState graph) clear).1
      change KeepsStore state.current.native _ ∧ _
      rw [same]
      refine ⟨handle_store_of_some runtime _ native _ handled, ?_,
        handle_preserves_accepted runtime _ native _ handled, ?_⟩
      · obtain ⟨event, _, ready, action, supported⟩ :=
          handle_config_mem_step runtime _ native _ handled
        change state.current.native.config.history.IsPrefix native.config.history
        rw [state.current.native.config.step_history _ _ _ _ supported]
        exact ⟨_, rfl⟩
      · exact handle_completed_subset runtime _ native _ handled
    · cases accepted
  environment state command next reached clear := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      have same := (PhaseRuntimeState.normalize_of_clear
        ({ state with current := state.current.environmentResult command native } :
          PhaseRuntimeState graph) clear).1
      change KeepsStore state.current.native _ ∧ _
      rw [same]
      refine ⟨environmentStep_store_of_some runtime _ native command supported,
        environmentStep_history_prefix runtime _ native command supported, ?_,
        environmentStep_completed_subset runtime _ native command supported⟩
      intro field candidate present
      change native.accepted field = some candidate
      rw [(environmentStep_tables runtime _ native command supported).1]
      exact present
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨fun _ _ present => present, ⟨[], by simp⟩, fun _ _ present => present,
        fun _ member => member⟩

end Vegas.EventGraphRuntime
