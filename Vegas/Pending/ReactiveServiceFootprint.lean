/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceSelection

/-! # Events that a reserved service instruction can complete

Submission changes no game fields. Reserved inclusion can complete only its
addressed event, even when earlier responses were arbitrary. The lookup uses
authenticated envelope identity from the existing submission audit.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def ServiceInstruction.targets (instruction : ServiceInstruction graph)
    (query : graph.EventId) : Bool :=
  match instruction with
  | .includeLatest event _ | .sample event | .expire event => event == query
  | .wire => true
  | _ => false

private theorem handle_unfinished (runtime : EventGraphRuntime graph)
    (before after : State graph) (message : Message Player (Payload graph))
    (query : graph.EventId) (untouched : message.payload.event? graph ≠ some query)
    (unfinished : query ∉ before.config.cut.completed)
    (accepted : handle runtime before message = some after) :
    query ∉ after.config.cut.completed := by
  obtain ⟨event, address, ready, action, member⟩ :=
    handle_config_mem_step runtime before after message accepted
  have different : query ≠ event := by intro same; subst event; exact untouched address
  rw [before.config.step_cut event ready action after.config member]
  simpa only [EventOrder.Cut.complete, Finset.mem_insert, not_or] using
    And.intro different unfinished

omit [DecidableEq Player] in
private theorem maintenance_unfinished (runtime : EventGraphRuntime graph)
    (before after : State graph) (command : EnvironmentCommand graph)
    (query : graph.EventId)
    (untouched : command ≠ .executeSample query ∧ command ≠ .expire query)
    (unfinished : query ∉ before.config.cut.completed)
    (moved : after ∈ (environmentStep runtime before command).support) :
    query ∉ after.config.cut.completed := by
  cases command with
  | grant event | advanceClock =>
      cases FinDist.mem_support_pure.mp moved
      exact unfinished
  | executeSample event =>
      obtain ⟨_, effect⟩ :=
        environmentStep_executeSample_config_activated runtime before after event moved
      rcases effect with ⟨same, _⟩ | ⟨ready, action, member, _⟩
      · rwa [same]
      · rw [before.config.step_cut event ready action after.config member]
        have different : query ≠ event := by
          intro same; subst event; exact untouched.1 rfl
        simpa only [EventOrder.Cut.complete, Finset.mem_insert, not_or] using
          And.intro different unfinished
  | expire event =>
      obtain ⟨_, effect⟩ :=
        environmentStep_expire_config_activated runtime before after event moved
      rcases effect with ⟨same, _⟩ | ⟨ready, action, member, _⟩
      · rwa [same]
      · rw [before.config.step_cut event ready action after.config member]
        have different : query ≠ event := by
          intro same; subst event; exact untouched.2 rfl
        simpa only [EventOrder.Cut.complete, Finset.mem_insert, not_or] using
          And.intro different unfinished

theorem reactive_instruction_unfinished (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks)
    (before after : (runtime.reactiveApplication leaks).Execution)
    (instruction : ServiceInstruction graph)
    (command : (runtime.reactiveApplication leaks).Command)
    (query : graph.EventId)
    (audit : before.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (untouched : instruction.targets query = false)
    (unfinished : query ∉ before.application.config.cut.completed)
    (selected : command ∈ (runtime.interactionInstruction leaks network
      before.environmentRecall (before.observeEnvironment (runtime.reactiveApplication leaks))
        instruction).support)
    (moved : after ∈ (before.environmentStep (runtime.reactiveApplication leaks) command).support) :
    query ∉ after.application.config.cut.completed := by
  cases instruction with
  | wire => cases untouched
  | player who =>
      cases FinDist.mem_support_pure.mp selected
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ moved
      obtain ⟨_, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact unfinished
  | includeLatest event who =>
      cases FinDist.mem_support_pure.mp selected
      have different : event ≠ query := by simpa only [ServiceInstruction.targets,
        beq_eq_false_iff_ne] using untouched
      unfold reactiveLatest at moved
      split at moved
      · simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at moved
        cases FinDist.mem_support_pure.mp moved
        exact unfinished
      · rename_i message found
        have good := List.find?_some found
        have addressed : message.payload.call.event? graph = some event :=
          (of_decide_eq_true good).2.1
        have pending := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
        have lookup := audit.lookup_of_mem (runtime.reactiveApplication leaks)
          ReactivePlayerView.publicView before message pending
        simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
          FinDist.mem_support_pure] at moved
        subst after
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          lookup]
        change query ∉ ((handle runtime before.application
          ⟨message.id, message.payload.call⟩).getD before.application).config.cut.completed
        cases handled : handle runtime before.application ⟨message.id, message.payload.call⟩ with
        | none => exact unfinished
        | some state =>
            exact handle_unfinished runtime _ state _ query
              (by rw [addressed]; exact fun same => different (Option.some.inj same))
              unfinished handled
  | grant event | tick | sample event | expire event =>
      cases FinDist.mem_support_pure.mp selected
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ moved
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      apply maintenance_unfinished runtime _ state _ query _ unfinished changed
      all_goals simp_all [ServiceInstruction.targets]

end Vegas.EventGraphRuntime
