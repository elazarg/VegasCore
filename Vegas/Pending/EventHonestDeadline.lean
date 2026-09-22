/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventServiceCompletion

/-! # Deadline protection for honest event service epochs -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

namespace State

/-- Every live strategic activation is at most one block old. -/
def ActivationAgeOne (state : State graph) : Prop :=
  ∀ event entered, state.activatedAt event = some entered →
    event ∉ state.config.cut.completed → state.clock - entered ≤ 1

/-- A transition either retains a live activation timestamp or creates it no
earlier than the transition's entry clock. -/
def ActivationOrigin (before after : State graph) : Prop :=
  ∀ event entered, after.activatedAt event = some entered →
    event ∉ after.config.cut.completed →
      before.activatedAt event = some entered ∨ before.clock ≤ entered

omit [DecidableEq Player] in
theorem activationOrigin_of_activatedEq {before after : State graph}
    (activatedEq : after.activatedAt = before.activatedAt) :
    ActivationOrigin before after := by
  intro event entered activated unfinished
  exact Or.inl (by simpa only [activatedEq] using activated)

omit [DecidableEq Player] in
theorem activationOrigin_refresh (before : State graph) (config : graph.Config) :
    ActivationOrigin before
      { before with
        config
        activatedAt := refreshActivated config before.clock before.activatedAt } := by
  intro event entered activated unfinished
  change refreshActivated config before.clock before.activatedAt event = some entered at activated
  unfold refreshActivated at activated
  split at activated
  · rename_i ready
    cases actor : graph.actor? event with
    | none => simp [actor] at activated
    | some owner =>
        rw [actor] at activated
        cases prior : before.activatedAt event with
        | none =>
            right
            have same : before.clock = entered := by simpa [prior] using activated
            omega
        | some priorEntered =>
            left
            have same : priorEntered = entered := by simpa [prior] using activated
            exact congrArg some same
  · simp_all

omit [DecidableEq Player] in
theorem activationOrigin_of_refreshEq {before after : State graph}
    (activated : after.activatedAt =
      refreshActivated after.config before.clock before.activatedAt) :
    ActivationOrigin before after := by
  intro event entered value unfinished
  rw [activated] at value
  exact activationOrigin_refresh before after.config event entered value unfinished

omit [DecidableEq Player] in
theorem ActivationOrigin.trans {before middle after : State graph}
    (first : ActivationOrigin before middle)
    (second : ActivationOrigin middle after)
    (clock : before.clock ≤ middle.clock)
    (completed : middle.config.cut.completed ⊆ after.config.cut.completed) :
    ActivationOrigin before after := by
  intro event entered activated unfinished
  rcases second event entered activated unfinished with retained | created
  · have middleUnfinished : event ∉ middle.config.cut.completed := by
      intro done
      exact unfinished (completed done)
    exact first event entered retained middleUnfinished
  · exact Or.inr (clock.trans created)

theorem initial_activationAgeOne (inputs : graph.Inputs) :
    (State.initial inputs).ActivationAgeOne := by
  intro event entered activated unfinished
  have le := (State.initial_invariant inputs).activated_le event entered activated
  change 0 - entered ≤ 1
  omega

omit [DecidableEq Player] in
/-- A single protected event retains its age bound through a clock-free
transition. Unrelated events may already be overdue. -/
theorem age_le_one_of_zero_progress {inputs : graph.Inputs}
    {before after : State graph} (event : graph.EventId)
    (age : ∀ entered, before.activatedAt event = some entered →
      event ∉ before.config.cut.completed → before.clock - entered ≤ 1)
    (progress : State.ServiceProgress inputs 0 before after)
    (origin : ActivationOrigin before after)
    (entered : Nat) (activated : after.activatedAt event = some entered)
    (unfinished : event ∉ after.config.cut.completed) : after.clock - entered ≤ 1 := by
  rcases origin event entered activated unfinished with retained | created
  · have oldAge := age entered retained (fun done => unfinished (progress.completed done))
    rw [progress.clock]
    simpa using oldAge
  · rw [progress.clock]
    omega

omit [DecidableEq Player] in
/-- A clock-free prefix preserves the one-block age bound when new timestamp
origins are accounted for. -/
theorem ActivationAgeOne.of_zero_progress {inputs : graph.Inputs}
    {before after : State graph}
    (age : before.ActivationAgeOne)
    (progress : State.ServiceProgress inputs 0 before after)
    (origin : ActivationOrigin before after) : after.ActivationAgeOne := by
  intro event entered activated unfinished
  exact age_le_one_of_zero_progress event (age event) progress origin entered activated unfinished

omit [DecidableEq Player] in
/-- Servicing one event's entry activation suffices to protect its next
deadline. No completion or age condition is imposed on other players. -/
theorem age_le_one_after_epoch {inputs : graph.Inputs}
    {before after : State graph} (event : graph.EventId)
    (progress : State.ServiceProgress inputs 1 before after)
    (origin : ActivationOrigin before after)
    (serviced : ∀ entered, before.activatedAt event = some entered →
      event ∈ after.config.cut.completed)
    (entered : Nat) (activated : after.activatedAt event = some entered)
    (unfinished : event ∉ after.config.cut.completed) : after.clock - entered ≤ 1 := by
  rcases origin event entered activated unfinished with retained | created
  · exact False.elim (unfinished (serviced entered retained))
  · rw [progress.clock]
    omega

omit [DecidableEq Player] in
/-- If one epoch completes every event that was already activated at entry,
then every live activation after its unique tick was created during that epoch
and is at most one block old. -/
theorem activationAgeOne_after_epoch {inputs : graph.Inputs}
    {before after : State graph}
    (progress : State.ServiceProgress inputs 1 before after)
    (origin : ActivationOrigin before after)
    (serviced : ∀ event entered, before.activatedAt event = some entered →
      event ∈ after.config.cut.completed) : after.ActivationAgeOne := by
  intro event entered activated unfinished
  exact age_le_one_after_epoch event progress origin (serviced event) entered activated unfinished

omit [DecidableEq Player] in
/-- The one-block boundary invariant and a feasible runtime make every live
strategic event timely. -/
theorem ActivationAgeOne.withinDeadline (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible) {state : State graph}
    (age : state.ActivationAgeOne) (event : graph.EventId) (entered : Nat)
    (activated : state.activatedAt event = some entered)
    (unfinished : event ∉ state.config.cut.completed) :
    state.WithinDeadline runtime event :=
  withinDeadline_of_age_le_one runtime feasible state event entered activated
    (age event entered activated unfinished)

end State

private theorem environmentPolicyStep_activationOrigin
    (runtime : EventGraphRuntime graph)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (member : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    State.ActivationOrigin execution.native.application next.native.application := by
  have native : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [MessageApplication.environmentStep_native] at native
  cases command with
  | deliver observer id | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      apply State.activationOrigin_of_activatedEq
      simpa only using congrArg
        (fun state : runtime.application.State => state.application.activatedAt) native
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      cases lookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id lookup] at native
          apply State.activationOrigin_of_activatedEq
          simpa only using congrArg
            (fun state : runtime.application.State => state.application.activatedAt) native
      | some message =>
          cases accepted : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message
                lookup accepted] at native
              apply State.activationOrigin_of_activatedEq
              simpa only using congrArg
                (fun state : runtime.application.State => state.application.activatedAt) native
          | some state =>
              rw [runtime.application.includePending_accept execution.native id message state
                lookup accepted] at native
              have same : next.native.application = state := by
                simpa using congrArg
                  (fun result : runtime.application.State => result.application) native
              rw [same]
              have facts := runtime.handle_clock_activated execution.native.application state
                message accepted
              exact State.activationOrigin_of_refreshEq facts.2
  | application command =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at native
      obtain ⟨state, supported, same⟩ := native
      have nextEq := congrArg
        (fun result : runtime.application.State => result.application) same.symm
      rw [nextEq]
      cases command with
      | grant event =>
          apply State.activationOrigin_of_activatedEq
          change state ∈ (Vegas.EventGraphRuntime.environmentStep runtime
            execution.native.application (.grant event)).support at supported
          simp [Vegas.EventGraphRuntime.environmentStep] at supported
          subst state
          rfl
      | advanceClock =>
          apply State.activationOrigin_of_activatedEq
          change state ∈ (Vegas.EventGraphRuntime.environmentStep runtime
            execution.native.application .advanceClock).support at supported
          simp [Vegas.EventGraphRuntime.environmentStep] at supported
          subst state
          rfl
      | executeSample event =>
          obtain ⟨clock, stutter | step⟩ :=
            runtime.environmentStep_executeSample_config_activated
              execution.native.application state event supported
          · exact State.activationOrigin_of_activatedEq stutter.2
          · obtain ⟨ready, action, member, activated⟩ := step
            exact State.activationOrigin_of_refreshEq activated
      | expire event =>
          obtain ⟨clock, stutter | step⟩ :=
            runtime.environmentStep_expire_config_activated
              execution.native.application state event supported
          · exact State.activationOrigin_of_activatedEq stutter.2
          · obtain ⟨ready, action, member, activated⟩ := step
            exact State.activationOrigin_of_refreshEq activated

/-- Every concrete service instruction retains old live activation timestamps
or creates new ones no earlier than its entry clock. -/
theorem serviceStep_activationOrigin (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (member : next ∈ (runtime.serviceStep players wire instruction execution).support) :
    State.ActivationOrigin execution.native.application next.native.application := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, member⟩ := member
      have native : next.native ∈
          ((runtime.application.playerStep who execution command).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨next, member, rfl⟩
      rw [MessageApplication.playerStep_native] at native
      cases command with
      | privateCommand command =>
        simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at native
        apply State.activationOrigin_of_activatedEq
        have nextEq := congrArg
          (fun state : runtime.application.State => state.application.activatedAt) native
        exact nextEq.trans
          (privateStep_facts execution.native.application who command).2.2
      | submit payload | replay id | wait =>
        simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at native
        apply State.activationOrigin_of_activatedEq
        simpa only [application, submitStep_activatedAt] using congrArg
          (fun state : runtime.application.State => state.application.activatedAt) native
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨command, _, member⟩ := member
      exact environmentPolicyStep_activationOrigin runtime execution next
        (command.toEnvironmentCommand runtime.application) member
  | grant event | includeLatest event owner | sample event | tick | expire event =>
      exact environmentPolicyStep_activationOrigin runtime execution next _ member

/-- Activation origins compose through every actual finite service plan. -/
theorem runServicePlan_activationOrigin (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (plan : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (member : next ∈ (runtime.runServicePlan players wire plan execution).support) :
    State.ActivationOrigin execution.native.application next.native.application := by
  induction plan generalizing execution with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst next
      exact State.activationOrigin_of_activatedEq rfl
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, headMem, tailMem⟩ := member
      have headProgress := runtime.serviceStep_facts inputs players wire instruction
        execution middle invariant headMem
      have tailProgress := runtime.runServicePlan_facts inputs players wire rest middle next
        headProgress.invariant tailMem
      exact (runtime.serviceStep_activationOrigin players wire instruction execution middle
        headMem).trans
          (ih middle headProgress.invariant tailMem)
          (by rw [headProgress.clock]; omega) tailProgress.completed

/-- Every supported adaptive service epoch has the operational activation
origin property. -/
theorem serviceEpoch_activationOrigin (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (member : next ∈ (runtime.serviceEpoch roster reactionRounds players wire order
      execution).support) :
    State.ActivationOrigin execution.native.application next.native.application := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at member
  obtain ⟨chosen, _, member⟩ := member
  exact runtime.runServicePlan_activationOrigin inputs players wire
    (epochPlan chosen roster reactionRounds) execution next invariant member

/-- A supported epoch that services every entry activation re-establishes the
one-block boundary invariant. -/
theorem serviceEpoch_activationAgeOne (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (member : next ∈ (runtime.serviceEpoch roster reactionRounds players wire order
      execution).support)
    (serviced : ∀ event entered,
      execution.native.application.activatedAt event = some entered →
        event ∈ next.native.application.config.cut.completed) :
    next.native.application.ActivationAgeOne := by
  exact State.activationAgeOne_after_epoch
    (runtime.serviceEpoch_facts inputs roster reactionRounds players wire order
      execution next invariant member)
    (runtime.serviceEpoch_activationOrigin inputs roster reactionRounds players wire order
      execution next invariant member) serviced

omit [DecidableEq Player] in
/-- A protected addressed event cannot expire, regardless of the age or
behavior of unrelated events. -/
theorem environmentStep_expire_eq_of_age (runtime : EventGraphRuntime graph)
    (state : State graph) (event : graph.EventId) (feasible : 2 ≤ runtime.deadline event)
    (age : ∀ entered, state.activatedAt event = some entered →
      event ∉ state.config.cut.completed → state.clock - entered ≤ 1) :
    environmentStep runtime state (.expire event) = FinDist.pure state := by
  by_cases ready : state.config.cut.Ready event
  · cases activated : state.activatedAt event with
    | none => exact runtime.environmentStep_expire_of_not_activated state event ready activated
    | some entered =>
        apply runtime.environmentStep_expire_of_not_due state event ready entered activated
        have ageBound := age entered activated ready.1
        omega
  · exact runtime.environmentStep_expire_of_not_ready state event ready

/-- At a protected event, the concrete expiry instruction leaves application
state unchanged. Other events may already be overdue. -/
theorem serviceStep_expire_application_eq (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (event : graph.EventId)
    (feasible : 2 ≤ runtime.deadline event)
    (execution next : runtime.application.PolicyExecution)
    (age : ∀ entered, execution.native.application.activatedAt event = some entered →
      event ∉ execution.native.application.config.cut.completed →
        execution.native.application.clock - entered ≤ 1)
    (member : next ∈
      (runtime.serviceStep players wire (.expire event) execution).support) :
    next.native.application = execution.native.application := by
  have native : next.native ∈
      ((runtime.application.environmentPolicyStep execution
        (.application (.expire event))).map MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [MessageApplication.environmentStep_native] at native
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.support_map, Set.mem_image] at native
  obtain ⟨state, supported, same⟩ := native
  change state ∈ (Vegas.EventGraphRuntime.environmentStep runtime
    execution.native.application (.expire event)).support at supported
  have applicationEq := congrArg
    (fun result : runtime.application.State => result.application) same.symm
  rw [applicationEq]
  rw [runtime.environmentStep_expire_eq_of_age execution.native.application event feasible age,
    FinDist.mem_support_pure] at supported
  exact supported

private theorem runServicePlan_expiry_list_application_eq
    (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible) (inputs : graph.Inputs)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (events : List graph.EventId)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (age : execution.native.application.ActivationAgeOne)
    (member : next ∈ (runtime.runServicePlan players wire
      (events.map .expire) execution).support) :
    next.native.application = execution.native.application := by
  induction events generalizing execution with
  | nil =>
      simp only [List.map_nil, runServicePlan, FinDist.mem_support_pure] at member
      exact congrArg (fun result => result.native.application) member
  | cons event rest ih =>
      simp only [List.map_cons, runServicePlan, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨middle, headMem, tailMem⟩ := member
      have middleEq := runtime.serviceStep_expire_application_eq players wire
        event (feasible event) execution middle (age event) headMem
      have middleInvariant : middle.native.application.Invariant inputs := by
        rw [middleEq]
        exact invariant
      have middleAge : middle.native.application.ActivationAgeOne := by
        rw [middleEq]
        exact age
      have tailEq := ih middle middleInvariant middleAge tailMem
      exact tailEq.trans middleEq

/-- The complete feasible expiry sweep is an application-level stutter from
an age-one invariant state. -/
theorem runServicePlan_expiry_application_eq (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible) (inputs : graph.Inputs)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.Invariant inputs)
    (age : execution.native.application.ActivationAgeOne)
    (member : next ∈ (runtime.runServicePlan players wire
      ((List.finRange graph.order.eventCount).map .expire) execution).support) :
    next.native.application = execution.native.application :=
  runServicePlan_expiry_list_application_eq runtime feasible inputs players wire
    (List.finRange graph.order.eventCount) execution next invariant age member

end Vegas.EventGraphRuntime
