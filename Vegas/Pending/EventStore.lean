/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant
import Vegas.Pending.EventServiceLaw
import Vegas.Pending.EventServiceProtocol
import Interaction.MessageApplicationPolicyLaws

/-! # Immutable event-store prefixes

Once a typed field is available, no native action changes its value. This
includes arbitrary player commands, malformed traffic, replay, and expiry.
Endpoint-conditioned replay may therefore read an earlier public result from
a later observation without adding that observation to a runtime policy.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

namespace EventGraphRuntime

/-- Any accepted packet retains every already stored typed value. -/
theorem handle_store_of_some (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : state.config.store field = some value) :
    next.config.store field = some value := by
  obtain ⟨event, _, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  exact state.config.step_store_of_some next.config event ready action member field value stored

omit [DecidableEq Player] in
/-- Chance, clocks, grants, and expiry preserve every field already present. -/
theorem environmentStep_store_of_some (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : state.config.store field = some value) :
    next.config.store field = some value := by
  cases command with
  | grant event | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      exact stored
  | executeSample event =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_executeSample_config_activated runtime state next event member
      · rw [stutter.1]
        exact stored
      · obtain ⟨ready, action, member, _⟩ := step
        exact state.config.step_store_of_some next.config event ready action member
          field value stored
  | expire event =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_expire_config_activated runtime state next event member
      · rw [stutter.1]
        exact stored
      · obtain ⟨ready, action, member, _⟩ := step
        exact state.config.step_store_of_some next.config event ready action member
          field value stored

omit [DecidableEq Player] in
/-- An environment operation only appends semantic completions; it cannot
remove or replace an action already recorded in the graph history. -/
theorem environmentStep_history_prefix (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support) :
    state.config.history.IsPrefix next.config.history := by
  have fromStep (event : graph.EventId) (ready : state.config.cut.Ready event)
      (action : graph.Action event)
      (supported : next.config ∈ (state.config.step event ready action).support) :
      state.config.history.IsPrefix next.config.history := by
    rw [state.config.step_history event ready action next.config supported]
    exact ⟨_, rfl⟩
  cases command with
  | grant event | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      exact ⟨[], by simp⟩
  | executeSample event =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_executeSample_config_activated runtime state next event member
      · rw [stutter.1]
      · obtain ⟨ready, action, supported, _⟩ := step
        exact fromStep event ready action supported
  | expire event =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_expire_config_activated runtime state next event member
      · rw [stutter.1]
      · obtain ⟨ready, action, supported, _⟩ := step
        exact fromStep event ready action supported

/-- Arbitrary native traces extend the chronological semantic action history. -/
theorem applicationRun_history_prefix (runtime : EventGraphRuntime graph)
    (state next : runtime.application.State) (actions : List runtime.application.Action)
    (member : next ∈ (runtime.application.run actions state).support) :
    state.application.config.history.IsPrefix next.application.config.history := by
  apply runtime.application.run_application_invariant
    (fun current => state.application.config.history.IsPrefix current.config.history)
    _ _ _ state next actions ⟨[], by simp⟩ member
  · intro current who command prior
    change state.application.config.history.IsPrefix
      (privateStep current who command).config.history
    rw [(privateStep_facts current who command).1]
    exact prior
  · intro current message after prior accepted
    obtain ⟨event, _, ready, action, supported⟩ :=
      handle_config_mem_step runtime current after message accepted
    rw [current.config.step_history event ready action after.config supported]
    exact prior.trans ⟨_, rfl⟩
  · intro current command after prior supported
    exact prior.trans (environmentStep_history_prefix runtime current after command supported)

/-- Arbitrary native traces retain their initially available typed fields. -/
theorem applicationRun_store_of_some (runtime : EventGraphRuntime graph)
    (state next : runtime.application.State) (actions : List runtime.application.Action)
    (member : next ∈ (runtime.application.run actions state).support)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : state.application.config.store field = some value) :
    next.application.config.store field = some value := by
  exact runtime.application.run_application_invariant
    (fun current => current.config.store field = some value)
    (fun current who command present => by
      change (privateStep current who command).config.store field = some value
      rw [(privateStep_facts current who command).1]
      exact present)
    (fun current message after present accepted =>
      handle_store_of_some runtime current after message accepted field value present)
    (fun current command after present supported =>
      environmentStep_store_of_some runtime current after command supported field value present)
    state next actions stored member

/-- Runtime policies cannot rewrite an available field, even when they retain
the complete local history and observe messages before inclusion. -/
theorem runPolicies_store_of_some (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (before after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.application.runPolicies players environment schedule before).support)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : before.native.application.config.store field = some value) :
    after.native.application.config.store field = some value := by
  obtain ⟨actions, _, supported⟩ := runtime.application.runPolicies_native_support
    players environment schedule before after member
  exact runtime.applicationRun_store_of_some before.native after.native actions supported
    field value stored

/-- The actual adaptive service preserves every previously available field. -/
theorem runService_store_of_some (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (before after : runtime.application.PolicyExecution)
    (member : after ∈
      (runtime.runService roster reactionRounds players wire order count before).support)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : before.native.application.config.store field = some value) :
    after.native.application.config.store field = some value := by
  obtain ⟨actions, _, supported⟩ := runtime.runService_native_support
    roster reactionRounds players wire order count before after member
  exact runtime.applicationRun_store_of_some before.native after.native actions supported
    field value stored

/-- The same immutable-prefix fact holds between arbitrary service-plan
positions, including a position inside an epoch or its reaction slots. -/
theorem runServicePlan_store_of_some (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : before.native.application.config.store field = some value) :
    after.native.application.config.store field = some value := by
  obtain ⟨actions, _, supported⟩ := runtime.runServicePlan_native_support
    players wire plan before after member
  exact runtime.applicationRun_store_of_some before.native after.native actions supported
    field value stored

/-- A supported adaptive service suffix extends the recorded graph history. -/
theorem runService_history_prefix (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (before after : runtime.application.PolicyExecution)
    (member : after ∈
      (runtime.runService roster reactionRounds players wire order count before).support) :
    before.native.application.config.history.IsPrefix after.native.application.config.history := by
  obtain ⟨actions, _, supported⟩ := runtime.runService_native_support
    roster reactionRounds players wire order count before after member
  exact runtime.applicationRun_history_prefix before.native after.native actions supported

/-- Semantic recall also grows monotonically between positions inside an epoch. -/
theorem runServicePlan_history_prefix (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    before.native.application.config.history.IsPrefix after.native.application.config.history := by
  obtain ⟨actions, _, supported⟩ := runtime.runServicePlan_native_support
    players wire plan before after member
  exact runtime.applicationRun_history_prefix before.native after.native actions supported

/-- A small service-control step records only native transitions; order
selection leaves the native execution, including its histories, unchanged. -/
theorem serviceControlStep_native_support (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : ServiceControl runtime)
    (member : after ∈
      (runtime.serviceControlStep roster reactionRounds players wire order before).support) :
    ∃ suffix, after.execution.nativeTrace = before.execution.nativeTrace ++ suffix ∧
      after.execution.native ∈
        (runtime.application.run suffix before.execution.native).support := by
  rcases runtime.serviceControlStep_cases roster reactionRounds players wire order before after
    member with ⟨_, _, same⟩ | ⟨epochs, chosen, _, _, _, same⟩ | instruction
  · subst after
    exact ⟨[], by simp⟩
  · subst after
    exact ⟨[], by simp⟩
  · obtain ⟨instruction, _, _, _, _, supported⟩ := instruction
    exact runtime.serviceStep_native_support players wire instruction before.execution
      after.execution supported

/-- Every small-step service prefix retains its exact native trace witness. -/
theorem runServiceControlSteps_native_support (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (fuel : Nat) (before after : ServiceControl runtime)
    (member : after ∈
      (runtime.runServiceControlSteps roster reactionRounds players wire order
        fuel before).support) :
    ∃ suffix, after.execution.nativeTrace = before.execution.nativeTrace ++ suffix ∧
      after.execution.native ∈
        (runtime.application.run suffix before.execution.native).support := by
  induction fuel generalizing before with
  | zero =>
      simp only [runServiceControlSteps, FinDist.mem_support_pure] at member
      subst after
      exact ⟨[], by simp⟩
  | succ fuel ih =>
      simp only [runServiceControlSteps] at member
      split at member
      · simp only [FinDist.mem_support_pure] at member
        subst after
        exact ⟨[], by simp⟩
      · simp only [FinDist.support_bind, Set.mem_iUnion] at member
        obtain ⟨middle, firstMem, restMem⟩ := member
        obtain ⟨first, firstTrace, firstRun⟩ := runtime.serviceControlStep_native_support
          roster reactionRounds players wire order before middle firstMem
        obtain ⟨second, secondTrace, secondRun⟩ := ih middle restMem
        refine ⟨first ++ second, ?_, ?_⟩
        · rw [secondTrace, firstTrace, List.append_assoc]
        · rw [runtime.application.run_append, FinDist.support_bind]
          simp only [Set.mem_iUnion]
          exact ⟨middle.execution.native, firstRun, secondRun⟩

theorem serviceControlStep_store_of_some (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : ServiceControl runtime)
    (member : after ∈
      (runtime.serviceControlStep roster reactionRounds players wire order before).support)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : before.execution.native.application.config.store field = some value) :
    after.execution.native.application.config.store field = some value := by
  obtain ⟨actions, _, supported⟩ := runtime.serviceControlStep_native_support
    roster reactionRounds players wire order before after member
  exact runtime.applicationRun_store_of_some before.execution.native after.execution.native
    actions supported field value stored

theorem runServiceControlSteps_store_of_some (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (fuel : Nat) (before after : ServiceControl runtime)
    (member : after ∈
      (runtime.runServiceControlSteps roster reactionRounds players wire order fuel before).support)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : before.execution.native.application.config.store field = some value) :
    after.execution.native.application.config.store field = some value := by
  obtain ⟨actions, _, supported⟩ := runtime.runServiceControlSteps_native_support
    roster reactionRounds players wire order fuel before after member
  exact runtime.applicationRun_store_of_some before.execution.native after.execution.native
    actions supported field value stored

theorem serviceControlStep_history_prefix (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : ServiceControl runtime)
    (member : after ∈
      (runtime.serviceControlStep roster reactionRounds players wire order before).support) :
    before.execution.native.application.config.history.IsPrefix
      after.execution.native.application.config.history := by
  obtain ⟨actions, _, supported⟩ := runtime.serviceControlStep_native_support
    roster reactionRounds players wire order before after member
  exact runtime.applicationRun_history_prefix before.execution.native after.execution.native
    actions supported

theorem runServiceControlSteps_history_prefix (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (fuel : Nat) (before after : ServiceControl runtime)
    (member : after ∈
      (runtime.runServiceControlSteps roster reactionRounds players wire order
        fuel before).support) :
    before.execution.native.application.config.history.IsPrefix
      after.execution.native.application.config.history := by
  obtain ⟨actions, _, supported⟩ := runtime.runServiceControlSteps_native_support
    roster reactionRounds players wire order fuel before after member
  exact runtime.applicationRun_history_prefix before.execution.native after.execution.native
    actions supported

end EventGraphRuntime
end Vegas
