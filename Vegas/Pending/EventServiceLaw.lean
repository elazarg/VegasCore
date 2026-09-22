/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventService
import Vegas.Pending.EventInvariant
import Interaction.MessageApplicationPolicyLaws

/-! # State and clock laws of the concrete event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A local execution invariant lifts through every concrete service plan. -/
theorem runServicePlan_invariant (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (invariant : runtime.application.PolicyExecution → Prop)
    (preserved : ∀ instruction before after, invariant before →
      after ∈ (runtime.serviceStep players wire instruction before).support → invariant after)
    (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution) (holds : invariant before)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    invariant after := by
  induction plan generalizing before with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst after
      exact holds
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, firstMem, restMem⟩ := member
      exact ih middle (preserved instruction before middle holds firstMem) restMem

/-- Local instruction preservation also suffices for adaptive order choices:
the order policy selects a plan but does not alter the execution itself. -/
theorem runService_invariant (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (invariant : runtime.application.PolicyExecution → Prop)
    (preserved : ∀ instruction before after, invariant before →
      after ∈ (runtime.serviceStep players wire instruction before).support → invariant after)
    (count : Nat) (before after : runtime.application.PolicyExecution) (holds : invariant before)
    (member : after ∈
      (runtime.runService roster reactionRounds players wire order count before).support) :
    invariant after := by
  induction count generalizing before with
  | zero =>
      simp only [runService, FinDist.mem_support_pure] at member
      subst after
      exact holds
  | succ count ih =>
      simp only [runService, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, epochMem, restMem⟩ := member
      simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at epochMem
      obtain ⟨chosen, _, planMem⟩ := epochMem
      exact ih middle (runtime.runServicePlan_invariant players wire invariant preserved
        (epochPlan chosen roster reactionRounds) before middle holds planMem) restMem

/-- A service instruction either stutters or executes one supported native
action. Policy choices introduce no transitions outside the application. -/
theorem serviceStep_native_step (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    after.native = before.native ∨
      ∃ action, after.native ∈ (runtime.application.step before.native action).support := by
  have environment (command : runtime.application.EnvironmentPolicyCommand)
      (supported : after ∈
        (runtime.application.environmentPolicyStep before command).support) :
      after.native = before.native ∨
        ∃ action, after.native ∈ (runtime.application.step before.native action).support := by
    have native : after.native ∈
        ((runtime.application.environmentPolicyStep before command).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨after, supported, rfl⟩
    rw [runtime.application.environmentStep_native] at native
    cases actionEq : command.toAction with
    | none =>
        left
        simpa only [actionEq, FinDist.mem_support_pure] using native
    | some action =>
        right
        exact ⟨action, by simpa only [actionEq] using native⟩
  cases instruction with
  | player who | wire =>
      exact runtime.application.invoke_native_step players
        (runtime.application.wireEnvironment wire) before after _ member
  | grant event | includeLatest event owner | sample event | tick | expire event =>
      exact environment _ member

/-- The recorded suffix also retains the exact action labels of that step. -/
theorem serviceStep_native_support (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    ∃ suffix, after.nativeTrace = before.nativeTrace ++ suffix ∧
      after.native ∈ (runtime.application.run suffix before.native).support := by
  cases instruction with
  | player who | wire =>
      exact runtime.application.invoke_native_support players
        (runtime.application.wireEnvironment wire) before after _ member
  | grant event | includeLatest event owner | sample event | tick | expire event =>
      exact runtime.application.environmentStep_native_support before _ after member

/-- A concrete service plan retains its complete native trace as an execution
witness, including private work, pending submissions, and rejected traffic. -/
theorem runServicePlan_native_support (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    ∃ suffix, after.nativeTrace = before.nativeTrace ++ suffix ∧
      after.native ∈ (runtime.application.run suffix before.native).support := by
  induction plan generalizing before with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst after
      exact ⟨[], by simp⟩
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, firstMem, restMem⟩ := member
      obtain ⟨first, firstTrace, firstRun⟩ :=
        runtime.serviceStep_native_support players wire instruction before middle firstMem
      obtain ⟨second, secondTrace, secondRun⟩ := ih middle restMem
      refine ⟨first ++ second, ?_, ?_⟩
      · rw [secondTrace, firstTrace, List.append_assoc]
      · rw [runtime.application.run_append, FinDist.support_bind]
        simp only [Set.mem_iUnion]
        exact ⟨middle.native, firstRun, secondRun⟩

/-- Publicly choosing an epoch order changes which native trace is executed,
not which native transitions exist. -/
theorem serviceEpoch_native_support (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : runtime.application.PolicyExecution)
    (member : after ∈
      (runtime.serviceEpoch roster reactionRounds players wire order before).support) :
    ∃ suffix, after.nativeTrace = before.nativeTrace ++ suffix ∧
      after.native ∈ (runtime.application.run suffix before.native).support := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at member
  obtain ⟨chosen, _, supported⟩ := member
  exact runtime.runServicePlan_native_support players wire
    (epochPlan chosen roster reactionRounds) before after supported

/-- Every supported adaptive service run has the exact appended native trace
as its operational witness. No restriction on player or wire policies is needed. -/
theorem runService_native_support (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (before after : runtime.application.PolicyExecution)
    (member : after ∈
      (runtime.runService roster reactionRounds players wire order count before).support) :
    ∃ suffix, after.nativeTrace = before.nativeTrace ++ suffix ∧
      after.native ∈ (runtime.application.run suffix before.native).support := by
  induction count generalizing before with
  | zero =>
      simp only [runService, FinDist.mem_support_pure] at member
      subst after
      exact ⟨[], by simp⟩
  | succ count ih =>
      simp only [runService, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, firstMem, restMem⟩ := member
      obtain ⟨first, firstTrace, firstRun⟩ := runtime.serviceEpoch_native_support
        roster reactionRounds players wire order before middle firstMem
      obtain ⟨second, secondTrace, secondRun⟩ := ih middle restMem
      refine ⟨first ++ second, ?_, ?_⟩
      · rw [secondTrace, firstTrace, List.append_assoc]
      · rw [runtime.application.run_append, FinDist.support_bind]
        simp only [Set.mem_iUnion]
        exact ⟨middle.native, firstRun, secondRun⟩

namespace State

/-- Proved transition facts: completed events persist, time advances by the
specified number of ticks, and a live event never loses its original deadline. -/
structure ServiceProgress (inputs : graph.Inputs) (ticks : Nat)
    (before after : State graph) : Prop where
  invariant : after.Invariant inputs
  completed : before.config.cut.completed ⊆ after.config.cut.completed
  clock : after.clock = before.clock + ticks
  activated : ∀ event entered, before.activatedAt event = some entered →
    event ∉ after.config.cut.completed → after.activatedAt event = some entered

omit [DecidableEq Player] in
theorem ServiceProgress.refl {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) : ServiceProgress inputs 0 state state :=
  ⟨invariant, Finset.Subset.refl _, by omega, fun _ _ same _ => same⟩

omit [DecidableEq Player] in
theorem ServiceProgress.trans {inputs : graph.Inputs} {first second : Nat}
    {before middle after : State graph}
    (left : ServiceProgress inputs first before middle)
    (right : ServiceProgress inputs second middle after) :
    ServiceProgress inputs (first + second) before after := by
  refine ⟨right.invariant, left.completed.trans right.completed, ?_, ?_⟩
  · rw [right.clock, left.clock, Nat.add_assoc]
  · intro event entered activated unfinished
    exact right.activated event entered
      (left.activated event entered activated (fun done => unfinished (right.completed done)))
      unfinished

omit [DecidableEq Player] in
theorem ServiceProgress.ready_or_completed {inputs : graph.Inputs} {ticks : Nat}
    {before after : State graph} (progress : ServiceProgress inputs ticks before after)
    (event : graph.EventId) (ready : before.config.cut.Ready event) :
    event ∈ after.config.cut.completed ∨ after.config.cut.Ready event := by
  by_cases done : event ∈ after.config.cut.completed
  · exact Or.inl done
  · exact Or.inr ⟨done, ready.2.trans progress.completed⟩

end State

omit [DecidableEq Player] in
/-- The deadline configuration leaves an event enabled during one epoch
eligible for inclusion throughout the following clock-free service sweep. -/
theorem withinDeadline_of_age_le_one (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible) (state : State graph) (event : graph.EventId)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (age : state.clock - entered ≤ 1) : state.WithinDeadline runtime event := by
  have bound := feasible event
  simp only [State.WithinDeadline, activated]
  omega

theorem privateStep_progress (inputs : graph.Inputs) (state : State graph)
    (who : Player) (command : PrivateCommand graph) (invariant : state.Invariant inputs) :
    State.ServiceProgress inputs 0 state (privateStep state who command) := by
  obtain ⟨config, clock, activated⟩ := privateStep_facts state who command
  refine ⟨privateStep_invariant state invariant who command, ?_, by simpa using clock, ?_⟩
  · rw [config]
  · intro event entered value _
    rw [activated]
    exact value

private theorem handle_progress (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (state next : State graph)
    (message : Message Player (Payload graph)) (invariant : state.Invariant inputs)
    (accepted : handle runtime state message = some next) :
    State.ServiceProgress inputs 0 state next := by
  refine ⟨handle_invariant runtime state next message invariant accepted,
    handle_completed_subset runtime state next message accepted, ?_, ?_⟩
  · simpa using (handle_clock_activated runtime state next message accepted).1
  · exact handle_activatedAt_of_not_completed runtime state next message invariant accepted

private theorem include_progress (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (state : runtime.application.State)
    (id : MessageId Player) (invariant : state.application.Invariant inputs) :
    State.ServiceProgress inputs 0 state.application
      (runtime.application.includePending state id).application := by
  cases found : state.pool.lookup id with
  | none =>
      rw [runtime.application.includePending_missing state id found]
      exact .refl invariant
  | some message =>
      cases accepted : runtime.application.handle state.application message with
      | none =>
          rw [runtime.application.includePending_reject state id message found accepted]
          exact .refl invariant
      | some next =>
          rw [runtime.application.includePending_accept state id message next found accepted]
          exact handle_progress runtime inputs state.application next message invariant accepted

theorem playerStep_progress (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (who : Player)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (invariant : execution.native.application.Invariant inputs)
    (member : next ∈ (runtime.application.playerStep who execution command).support) :
    State.ServiceProgress inputs 0 execution.native.application next.native.application := by
  have native : next.native ∈ ((runtime.application.playerStep who execution command).map
      MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [MessageApplication.playerStep_native] at native
  cases command with
  | privateCommand command =>
      simp only [MessageApplication.PlayerCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      rw [native]
      exact privateStep_progress inputs execution.native.application who command invariant
  | submit payload =>
      simp only [MessageApplication.PlayerCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      rw [native]
      exact ⟨invariant.copy rfl rfl rfl, Finset.Subset.rfl, rfl, fun _ _ same _ => same⟩
  | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      rw [native]
      exact .refl invariant

private def commandTicks (runtime : EventGraphRuntime graph) :
    runtime.application.EnvironmentPolicyCommand → Nat
  | .application .advanceClock => 1
  | _ => 0

private theorem environmentPolicyStep_progress (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (invariant : execution.native.application.Invariant inputs)
    (member : next ∈ (runtime.application.environmentPolicyStep execution command).support) :
    State.ServiceProgress inputs (commandTicks runtime command)
      execution.native.application next.native.application := by
  have native : next.native ∈ ((runtime.application.environmentPolicyStep execution command).map
      MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [MessageApplication.environmentStep_native] at native
  cases command with
  | deliver observer id | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      rw [native]
      exact .refl invariant
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      rw [native]
      exact include_progress runtime inputs execution.native id invariant
  | application command =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at native
      obtain ⟨state, supported, native⟩ := native
      rw [← native]
      refine ⟨environmentStep_invariant runtime execution.native.application state command
        invariant supported,
        environmentStep_completed_subset runtime execution.native.application state command
          supported, ?_, ?_⟩
      · have clock := environmentStep_clock runtime execution.native.application state
          command supported
        cases command <;> simpa [commandTicks, EnvironmentCommand.clockTicks] using clock
      · exact environmentStep_activatedAt_of_not_completed runtime
          execution.native.application state command invariant supported

/-- Every supported concrete service instruction preserves the invariant,
extends the completed cut, and has exactly its advertised clock effect. -/
theorem serviceStep_facts (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (member : next ∈ (runtime.serviceStep players wire instruction execution).support) :
    State.ServiceProgress inputs instruction.ticks
      execution.native.application next.native.application := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, member⟩ := member
      exact playerStep_progress runtime inputs who execution next command invariant member
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨command, _, member⟩ := member
      have progress := environmentPolicyStep_progress runtime inputs execution next
        (command.toEnvironmentCommand runtime.application) invariant member
      cases command <;> exact progress
  | grant event | sample event | tick | expire event =>
      exact environmentPolicyStep_progress runtime inputs execution next _ invariant member
  | includeLatest event owner =>
      have progress := environmentPolicyStep_progress runtime inputs execution next
        (runtime.latestEventSubmissionCommand event owner
          (MessageApplication.State.environmentView runtime.application execution.native))
        invariant member
      unfold latestEventSubmissionCommand at progress
      split at progress <;> exact progress

/-- Sequencing concrete service instructions retains their exact time budget
and never resets a still-live event's activation timestamp. -/
theorem runServicePlan_facts (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (member : next ∈ (runtime.runServicePlan players wire plan execution).support) :
    State.ServiceProgress inputs (serviceTicks plan)
      execution.native.application next.native.application := by
  induction plan generalizing execution with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst next
      exact .refl invariant
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, step, tail⟩ := member
      have head := serviceStep_facts runtime inputs players wire instruction execution middle
        invariant step
      exact head.trans (ih middle head.invariant tail)

/-- A complete adaptive service epoch advances exactly one block-clock tick. -/
theorem serviceEpoch_facts (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (member : next ∈ (runtime.serviceEpoch roster reactionRounds players wire order
      execution).support) :
    State.ServiceProgress inputs 1 execution.native.application next.native.application := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at member
  obtain ⟨chosen, _, member⟩ := member
  simpa only [epochPlan_ticks] using runServicePlan_facts runtime inputs players wire
    (epochPlan chosen roster reactionRounds) execution next invariant member

private theorem applicationStep_support (runtime : EventGraphRuntime graph)
    (execution next : runtime.application.PolicyExecution) (command : EnvironmentCommand graph)
    (member : next ∈ (runtime.application.environmentPolicyStep execution
      (.application command)).support) :
    next.native.application ∈ (environmentStep runtime execution.native.application
      command).support := by
  have native : next.native ∈ ((runtime.application.environmentPolicyStep execution
      (.application command)).map MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [MessageApplication.environmentStep_native] at native
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.support_map, Set.mem_image] at native
  obtain ⟨state, supported, same⟩ := native
  rw [← same]
  exact supported

/-- A reserved sample instruction completes a ready chance event. It executes
the graph's distribution rather than choosing a sample value. -/
theorem serviceStep_sample_complete (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (event : graph.EventId)
    (execution next : runtime.application.PolicyExecution)
    (ready : execution.native.application.config.cut.Ready event)
    (chance : graph.actor? event = none)
    (member : next ∈ (runtime.serviceStep players wire (.sample event) execution).support) :
    event ∈ next.native.application.config.cut.completed := by
  have supported := applicationStep_support runtime execution next (.executeSample event) member
  cases view : nodeView graph event with
  | bind owner payload outputEq codeEq | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq := congrArg EventGraph.EventCode.actor codeEq
      rw [EventGraph.EventCode.actor_cast outputEq (graph.nodes event)] at ownerEq
      change graph.actor? event = some owner at ownerEq
      simp only [chance] at ownerEq
      contradiction
  | sample payload law outputEq codeEq =>
      rw [environmentStep_executeSample_eq runtime execution.native.application event ready
        payload law outputEq codeEq view, FinDist.support_map] at supported
      obtain ⟨config, step, same⟩ := supported
      have configEq := congrArg State.config same
      rw [← configEq, EventGraph.Config.step_cut _ _ _ _ _ step]
      exact Finset.mem_insert_self _ _

/-- Every activated due strategic event completes when its reserved expiry
instruction executes, regardless of all player policies and pending traffic. -/
theorem serviceStep_expire_complete (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (event : graph.EventId)
    (execution next : runtime.application.PolicyExecution)
    (ready : execution.native.application.config.cut.Ready event)
    (strategic : (graph.actor? event).isSome = true)
    (entered : Nat) (activated : execution.native.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.native.application.clock - entered)
    (member : next ∈ (runtime.serviceStep players wire (.expire event) execution).support) :
    event ∈ next.native.application.config.cut.completed := by
  have supported := applicationStep_support runtime execution next (.expire event) member
  cases view : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have ownerEq := congrArg EventGraph.EventCode.actor codeEq
      rw [EventGraph.EventCode.actor_cast outputEq (graph.nodes event)] at ownerEq
      change graph.actor? event = none at ownerEq
      simp [ownerEq] at strategic
  | bind owner payload outputEq codeEq =>
      rw [environmentStep_expire_bind_eq runtime execution.native.application event ready
        entered activated due owner payload outputEq codeEq view,
        FinDist.mem_support_pure] at supported
      rw [supported]
      exact Finset.mem_insert_self _ _
  | resolve owner payload binding checks outputEq codeEq =>
      rw [environmentStep_expire_resolve_eq runtime execution.native.application event ready
        entered activated due owner payload binding checks outputEq codeEq view,
        FinDist.mem_support_pure] at supported
      rw [supported]
      exact Finset.mem_insert_self _ _

/-- Every environment-policy command preserves the private remembered-action
table.  Inclusion uses the application's packet-level cache frame. -/
theorem environmentPolicyStep_remembered
    (runtime : EventGraphRuntime graph)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (supported : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    next.native.application.remembered = execution.native.application.remembered := by
  have native : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  cases command with
  | deliver observer id | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      simpa only using congrArg
        (fun state : runtime.application.State => state.application.remembered) native
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      cases lookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id lookup] at native
          simpa only using congrArg
            (fun state : runtime.application.State => state.application.remembered) native
      | some message =>
          cases accepted : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message
                lookup accepted] at native
              simpa only using congrArg
                (fun state : runtime.application.State => state.application.remembered) native
          | some state =>
              rw [runtime.application.includePending_accept execution.native id message state
                lookup accepted] at native
              have nextEq : next.native.application = state := by
                simpa only using congrArg
                  (fun result : runtime.application.State => result.application) native
              rw [nextEq]
              exact runtime.handle_remembered execution.native.application state message accepted
  | application applicationCommand =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at native
      obtain ⟨state, stateMem, same⟩ := native
      have nextEq : next.native.application = state := by
        exact congrArg (fun result : runtime.application.State => result.application) same.symm
      rw [nextEq]
      exact environmentStep_remembered runtime execution.native.application state
        applicationCommand stateMem

end Vegas.EventGraphRuntime
