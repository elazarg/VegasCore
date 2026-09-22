/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication
import Interaction.MessageApplicationLaws

/-! # Reachability and activation invariants for event applications

The event-addressed pending runtime carries an ideal `EventGraph.Config` beside
its public message state.  This module records the small invariant needed by a
service proof: the configuration is graph-reachable, activation timestamps are
present exactly for ready strategic events, and no timestamp lies in the
future.  Candidate provenance and service policy obligations deliberately do
not belong to this invariant.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

namespace EventGraphRuntime

namespace State

/-- The runtime facts shared by message inclusion, chance execution, and
deadline expiry.  `inputs` fixes the separately supplied graph setup. -/
structure Invariant (inputs : graph.Inputs) (state : State graph) : Prop where
  reachable : state.config.Reachable inputs
  activated_iff : ∀ event,
    (state.activatedAt event).isSome = true ↔
      state.config.cut.Ready event ∧ (graph.actor? event).isSome = true
  activated_le : ∀ event entered,
    state.activatedAt event = some entered → entered ≤ state.clock

omit [DecidableEq Player] in
/-- Fields outside the graph configuration, clock, and activation table are
irrelevant to this invariant. -/
theorem Invariant.copy {inputs : graph.Inputs} {before after : State graph}
    (invariant : before.Invariant inputs)
    (configEq : after.config = before.config)
    (clockEq : after.clock = before.clock)
    (activatedEq : after.activatedAt = before.activatedAt) :
    after.Invariant inputs := by
  refine ⟨?_, ?_, ?_⟩
  · rw [configEq]
    exact invariant.reachable
  · intro event
    rw [activatedEq, configEq]
    exact invariant.activated_iff event
  · intro event entered activated
    rw [activatedEq] at activated
    rw [clockEq]
    exact invariant.activated_le event entered activated

omit [DecidableEq Player] in
@[simp] theorem refreshActivated_isSome (config : graph.Config) (clock : Nat)
    (prior : graph.EventId → Option Nat) (event : graph.EventId) :
    (refreshActivated config clock prior event).isSome = true ↔
      config.cut.Ready event ∧ (graph.actor? event).isSome = true := by
  unfold refreshActivated
  split
  · rename_i ready
    cases actor : graph.actor? event <;> simp_all
  · simp_all

omit [DecidableEq Player] in
theorem refreshActivated_le (config : graph.Config) (clock : Nat)
    (prior : graph.EventId → Option Nat)
    (priorLe : ∀ event entered, prior event = some entered → entered ≤ clock)
    (event : graph.EventId) (entered : Nat)
    (activated : refreshActivated config clock prior event = some entered) :
    entered ≤ clock := by
  by_cases ready : config.cut.Ready event
  · rw [refreshActivated, dite_eq_left ready] at activated
    cases actor : graph.actor? event with
    | none => simp [actor] at activated
    | some owner =>
        rw [actor] at activated
        cases previous : prior event with
        | none =>
            have same : clock = entered := by simpa [previous] using activated
            omega
        | some previousEntered =>
            have same : previousEntered = entered := by simpa [previous] using activated
            subst previousEntered
            exact priorLe event entered previous
  · simp [refreshActivated, ready] at activated

omit [DecidableEq Player] in
/-- Refreshing activation metadata around one supported graph step preserves
the invariant.  This is the common semantic core of accepted packets, samples,
and due expiries. -/
theorem Invariant.refreshStep {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (config : graph.Config)
    (member : config ∈ (state.config.step event ready action).support) :
    Invariant inputs
      { state with
        config
        activatedAt := refreshActivated config state.clock state.activatedAt } := by
  refine ⟨EventGraph.Config.Reachable.step invariant.reachable
    event ready action config member, ?_, ?_⟩
  · exact refreshActivated_isSome config state.clock state.activatedAt
  · intro query entered activated
    exact refreshActivated_le config state.clock state.activatedAt
      invariant.activated_le query entered activated

omit [DecidableEq Player] in
/-- A supported graph step can only enlarge the completed frontier. -/
theorem completed_subset_of_mem_step
    (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (next : graph.Config) (member : next ∈ (config.step event ready action).support) :
    config.cut.completed ⊆ next.cut.completed := by
  rw [config.step_cut event ready action next member]
  exact config.cut.completed_subset_complete event ready

omit [DecidableEq Player] in
/-- Refreshing retains an existing timestamp whenever the event remains ready
and strategic. -/
theorem refreshActivated_eq_of_ready (config : graph.Config) (clock : Nat)
    (prior : graph.EventId → Option Nat) (event : graph.EventId) (entered : Nat)
    (ready : config.cut.Ready event) (actor : (graph.actor? event).isSome = true)
    (activated : prior event = some entered) :
    refreshActivated config clock prior event = some entered := by
  unfold refreshActivated
  rw [dite_eq_left ready]
  cases actorEq : graph.actor? event with
  | none => simp [actorEq] at actor
  | some owner => simp [activated]

omit [DecidableEq Player] in
/-- A different completion cannot reset the timestamp of an event that was
ready before the step and is still unfinished afterwards. -/
theorem Invariant.refreshStep_activatedAt_of_not_completed
    {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) (completed query : graph.EventId)
    (ready : state.config.cut.Ready completed) (action : graph.Action completed)
    (config : graph.Config)
    (member : config ∈ (state.config.step completed ready action).support)
    (entered : Nat) (activated : state.activatedAt query = some entered)
    (unfinished : query ∉ config.cut.completed) :
    refreshActivated config state.clock state.activatedAt query = some entered := by
  have queryReady := (invariant.activated_iff query).mp (by simp [activated]) |>.1
  have actor := (invariant.activated_iff query).mp (by simp [activated]) |>.2
  have cutEq := state.config.step_cut completed ready action config member
  have different : query ≠ completed := by
    intro same
    subst query
    apply unfinished
    rw [cutEq, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have readyAfter : config.cut.Ready query := by
    rw [cutEq]
    exact queryReady.after_complete ready different
  exact refreshActivated_eq_of_ready config state.clock state.activatedAt
    query entered readyAfter actor activated

/-- The initial runtime state satisfies reachability and initializes precisely
the strategic events ready at the empty cut. -/
theorem initial_invariant (inputs : graph.Inputs) :
    (initial inputs).Invariant inputs := by
  refine ⟨EventGraph.Config.Reachable.initial, ?_, ?_⟩
  · intro event
    change (refreshActivated (EventGraph.Config.initial inputs) 0
      (fun _ => none) event).isSome = true ↔ _
    exact refreshActivated_isSome _ _ _ _
  · intro event entered activated
    change refreshActivated (EventGraph.Config.initial inputs) 0
      (fun _ => none) event = some entered at activated
    exact refreshActivated_le _ _ _ (by simp) event entered activated

end State

/-- Principal-local preparation and recall do not affect the graph execution,
clock, or activation frontier. -/
theorem privateStep_invariant {inputs : graph.Inputs} (state : State graph)
    (invariant : state.Invariant inputs) (who : Player)
    (command : PrivateCommand graph) :
    (privateStep state who command).Invariant inputs := by
  cases command with
  | prepare serial raw =>
      apply invariant.copy <;> rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · cases remembered : state.remembered event
        <;> apply invariant.copy <;> simp [privateStep, owned, remembered]
      · apply invariant.copy <;> simp [privateStep, owned]

/-- Private commands leave every graph/service timing field unchanged. -/
theorem privateStep_facts (state : State graph) (who : Player)
    (command : PrivateCommand graph) :
    (privateStep state who command).config = state.config ∧
      (privateStep state who command).clock = state.clock ∧
      (privateStep state who command).activatedAt = state.activatedAt := by
  cases command with
  | prepare serial raw => exact ⟨rfl, rfl, rfl⟩
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · cases remembered : state.remembered event <;>
          simp [privateStep, owned, remembered]
      · simp [privateStep, owned]

/-- Private commands cannot undo any completed event. -/
theorem privateStep_completed_subset (state : State graph) (who : Player)
    (command : PrivateCommand graph) :
    state.config.cut.completed ⊆
      (privateStep state who command).config.cut.completed := by
  rw [(privateStep_facts state who command).1]

/-- Accepted pending packets preserve the runtime invariant. -/
theorem handle_invariant {inputs : graph.Inputs} (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (invariant : state.Invariant inputs)
    (accepted : handle runtime state message = some next) :
    next.Invariant inputs := by
  obtain ⟨event, _, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  obtain ⟨clockEq, activatedEq⟩ :=
    handle_clock_activated runtime state next message accepted
  let refreshed : State graph :=
    { state with
      config := next.config
      activatedAt := State.refreshActivated next.config state.clock state.activatedAt }
  have refreshedInvariant : refreshed.Invariant inputs :=
    invariant.refreshStep event ready action next.config member
  apply refreshedInvariant.copy
  · rfl
  · exact clockEq
  · exact activatedEq

/-- Accepted pending packets can only enlarge the completed frontier. -/
theorem handle_completed_subset (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    state.config.cut.completed ⊆ next.config.cut.completed := by
  obtain ⟨_, _, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  exact State.completed_subset_of_mem_step state.config _ ready action next.config member

/-- An accepted packet preserves the timestamp of any event that remains
unfinished. -/
theorem handle_activatedAt_of_not_completed {inputs : graph.Inputs}
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph)) (invariant : state.Invariant inputs)
    (accepted : handle runtime state message = some next)
    (query : graph.EventId) (entered : Nat)
    (activated : state.activatedAt query = some entered)
    (unfinished : query ∉ next.config.cut.completed) :
    next.activatedAt query = some entered := by
  obtain ⟨completed, _, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  obtain ⟨_, activatedEq⟩ :=
    handle_clock_activated runtime state next message accepted
  rw [activatedEq]
  exact invariant.refreshStep_activatedAt_of_not_completed completed query ready action
    next.config member entered activated unfinished

omit [DecidableEq Player] in
/-- Environment commands advance the clock by exactly their declared tick
count.  Grant, sample, and expiry commands contribute zero ticks. -/
theorem environmentStep_clock (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support) :
    next.clock = state.clock + command.clockTicks := by
  cases command with
  | grant event =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      rfl
  | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      rfl
  | executeSample event =>
      obtain ⟨clockEq, _⟩ :=
        environmentStep_executeSample_config_activated runtime state next event member
      simpa [EnvironmentCommand.clockTicks] using clockEq
  | expire event =>
      obtain ⟨clockEq, _⟩ :=
        environmentStep_expire_config_activated runtime state next event member
      simpa [EnvironmentCommand.clockTicks] using clockEq

omit [DecidableEq Player] in
/-- Every supported environment command preserves graph reachability and exact
activation metadata. -/
theorem environmentStep_invariant {inputs : graph.Inputs}
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (command : EnvironmentCommand graph) (invariant : state.Invariant inputs)
    (member : next ∈ (environmentStep runtime state command).support) :
    next.Invariant inputs := by
  cases command with
  | grant event =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      exact invariant.copy rfl rfl rfl
  | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      refine ⟨invariant.reachable, invariant.activated_iff, ?_⟩
      intro event entered activated
      have := invariant.activated_le event entered activated
      change entered ≤ state.clock + 1
      omega
  | executeSample event =>
      obtain ⟨clockEq, effect⟩ :=
        environmentStep_executeSample_config_activated runtime state next event member
      rcases effect with ⟨configEq, activatedEq⟩ | ⟨ready, action, configMem, activatedEq⟩
      · exact invariant.copy configEq clockEq activatedEq
      · let refreshed : State graph :=
        { state with
            config := next.config
            activatedAt := State.refreshActivated next.config state.clock state.activatedAt }
        have refreshedInvariant : refreshed.Invariant inputs :=
          invariant.refreshStep event ready action next.config configMem
        exact refreshedInvariant.copy rfl clockEq activatedEq
  | expire event =>
      obtain ⟨clockEq, effect⟩ :=
        environmentStep_expire_config_activated runtime state next event member
      rcases effect with ⟨configEq, activatedEq⟩ | ⟨ready, action, configMem, activatedEq⟩
      · exact invariant.copy configEq clockEq activatedEq
      · let refreshed : State graph :=
        { state with
            config := next.config
            activatedAt := State.refreshActivated next.config state.clock state.activatedAt }
        have refreshedInvariant : refreshed.Invariant inputs :=
          invariant.refreshStep event ready action next.config configMem
        exact refreshedInvariant.copy rfl clockEq activatedEq

omit [DecidableEq Player] in
/-- Environment commands cannot undo completed events. -/
theorem environmentStep_completed_subset (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support) :
    state.config.cut.completed ⊆ next.config.cut.completed := by
  cases command with
  | grant event | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      exact Finset.Subset.rfl
  | executeSample event =>
      obtain ⟨_, effect⟩ :=
        environmentStep_executeSample_config_activated runtime state next event member
      rcases effect with ⟨configEq, _⟩ | ⟨ready, action, configMem, _⟩
      · rw [configEq]
      · exact State.completed_subset_of_mem_step state.config event ready action
          next.config configMem
  | expire event =>
      obtain ⟨_, effect⟩ :=
        environmentStep_expire_config_activated runtime state next event member
      rcases effect with ⟨configEq, _⟩ | ⟨ready, action, configMem, _⟩
      · rw [configEq]
      · exact State.completed_subset_of_mem_step state.config event ready action
          next.config configMem

omit [DecidableEq Player] in
/-- An environment command preserves the timestamp of every event that stays
unfinished. -/
theorem environmentStep_activatedAt_of_not_completed {inputs : graph.Inputs}
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (command : EnvironmentCommand graph) (invariant : state.Invariant inputs)
    (member : next ∈ (environmentStep runtime state command).support)
    (query : graph.EventId) (entered : Nat)
    (activated : state.activatedAt query = some entered)
    (unfinished : query ∉ next.config.cut.completed) :
    next.activatedAt query = some entered := by
  cases command with
  | grant event | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      exact activated
  | executeSample event =>
      obtain ⟨_, effect⟩ :=
        environmentStep_executeSample_config_activated runtime state next event member
      rcases effect with ⟨_, activatedEq⟩ | ⟨ready, action, configMem, activatedEq⟩
      · rw [activatedEq]
        exact activated
      · rw [activatedEq]
        exact invariant.refreshStep_activatedAt_of_not_completed event query ready action
          next.config configMem entered activated unfinished
  | expire event =>
      obtain ⟨_, effect⟩ :=
        environmentStep_expire_config_activated runtime state next event member
      rcases effect with ⟨_, activatedEq⟩ | ⟨ready, action, configMem, activatedEq⟩
      · rw [activatedEq]
        exact activated
      · rw [activatedEq]
        exact invariant.refreshStep_activatedAt_of_not_completed event query ready action
          next.config configMem entered activated unfinished

omit [DecidableEq Player] in
/-- A ready strategic event has a concrete activation timestamp. -/
theorem State.Invariant.activatedAt_eq_some_of_ready_actor
    {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) (event : graph.EventId)
    (ready : state.config.cut.Ready event)
    (strategic : (graph.actor? event).isSome = true) :
    ∃ entered, state.activatedAt event = some entered := by
  have present : (state.activatedAt event).isSome = true :=
    (invariant.activated_iff event).2 ⟨ready, strategic⟩
  cases activated : state.activatedAt event with
  | none => simp [activated] at present
  | some entered => exact ⟨entered, rfl⟩

/-- The complete native message transition preserves the event-runtime
invariant, including rejected and missing inclusions. -/
theorem applicationStep_invariant {inputs : graph.Inputs}
    (runtime : EventGraphRuntime graph)
    (state next : (application runtime).State)
    (action : (application runtime).Action)
    (invariant : state.application.Invariant inputs)
    (member : next ∈ ((application runtime).step state action).support) :
    next.application.Invariant inputs := by
  exact (application runtime).step_application_invariant
    (State.Invariant inputs)
    (fun application who command hinvariant =>
      privateStep_invariant application hinvariant who command)
    (fun application _ _ hinvariant => hinvariant.copy rfl rfl rfl)
    (fun application message result hinvariant accepted =>
      handle_invariant runtime application result message hinvariant accepted)
    (fun application command result hinvariant supported =>
      environmentStep_invariant runtime application result command hinvariant supported)
    state next action invariant member

/-- Runtime reachability survives arbitrary finite message-machine paths. -/
theorem applicationRun_invariant {inputs : graph.Inputs}
    (runtime : EventGraphRuntime graph)
    (state next : runtime.application.State) (actions : List runtime.application.Action)
    (invariant : state.application.Invariant inputs)
    (member : next ∈ (runtime.application.run actions state).support) :
    next.application.Invariant inputs := by
  exact runtime.application.run_application_invariant (State.Invariant inputs)
    (fun current who command holds => privateStep_invariant current holds who command)
    (fun _ _ _ holds => holds.copy rfl rfl rfl)
    (fun current message result holds accepted =>
      handle_invariant runtime current result message holds accepted)
    (fun current command result holds supported =>
      environmentStep_invariant runtime current result command holds supported)
    state next actions invariant member

/-- No native message action can undo a completed graph event. -/
theorem applicationStep_completed_subset (runtime : EventGraphRuntime graph)
    (state next : (application runtime).State)
    (action : (application runtime).Action)
    (member : next ∈ ((application runtime).step state action).support) :
    state.application.config.cut.completed ⊆
      next.application.config.cut.completed := by
  cases action with
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst next
      exact privateStep_completed_subset state.application who command
  | submit who payload | replay who id | deliver who id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst next
      exact Finset.Subset.rfl
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst next
      apply (application runtime).includePending_application_invariant
        (fun current => state.application.config.cut.completed ⊆
          current.config.cut.completed)
      · intro current message result subset accepted
        exact subset.trans (handle_completed_subset runtime current result message accepted)
      · exact Finset.Subset.rfl
  | environment command =>
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at member
      obtain ⟨result, supported, rfl⟩ := member
      exact environmentStep_completed_subset runtime state.application result command supported

end EventGraphRuntime
end Vegas
