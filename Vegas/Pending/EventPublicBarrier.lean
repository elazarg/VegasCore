/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.BarrierInformation
import Vegas.Pending.EventOpponentFrame

/-! # Ready public-event protection -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- While a public event is ready in a barrier-ordered graph, an application
packet authenticated as another player cannot be accepted. The packet payload
and any candidate handle it contains are unrestricted. -/
theorem handle_eq_none_of_other_actor_ready_public
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (state : State graph) (event : graph.EventId) (owner : Player)
    (isPublic : (graph.outputLayout event).IsPublic)
    (ready : state.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (message : Message Player (Payload graph))
    (different : message.sender ≠ owner) :
    handle runtime state message = none := by
  cases acceptedEq : handle runtime state message with
  | none => rfl
  | some next =>
      obtain ⟨addressed, addressedPayload, addressedReady, _, _⟩ :=
        handle_config_mem_step runtime state next message acceptedEq
      have same := ordered.ready_public_unique state.config.cut isPublic ready addressedReady
      subst addressed
      obtain ⟨handledEvent, handledPayload, handledActor⟩ :=
        handle_event_actor runtime state next message acceptedEq
      have handledSame : handledEvent = event := Option.some.inj
        (handledPayload.symm.trans addressedPayload)
      subst handledEvent
      rw [actor] at handledActor
      exact (different (Option.some.inj handledActor.symm)).elim

/-- Any accepted packet completes the unique ready public event. -/
theorem handle_completes_ready_public (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (state next : State graph) (event : graph.EventId)
    (isPublic : (graph.outputLayout event).IsPublic) (ready : state.config.cut.Ready event)
    (message : Message Player (Payload graph))
    (accepted : runtime.handle state message = some next) :
    event ∈ next.config.cut.completed := by
  obtain ⟨actual, _, actualReady, action, member⟩ :=
    runtime.handle_config_mem_step state next message accepted
  have same := ordered.ready_public_unique state.config.cut isPublic ready actualReady
  subst actual
  rw [state.config.step_cut event ready action next.config member]
  exact Finset.mem_insert_self _ _

/-- Environment execution cannot change the graph while its unique ready
public event remains unfinished. Clocks and grants may still change. -/
theorem environmentStep_config_of_ready_public_unfinished
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (state next : State graph) (event : graph.EventId)
    (isPublic : (graph.outputLayout event).IsPublic) (ready : state.config.cut.Ready event)
    (unfinished : event ∉ next.config.cut.completed) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support) :
    next.config = state.config := by
  have impossible (actual : graph.EventId) (actualReady : state.config.cut.Ready actual)
      (action : graph.Action actual)
      (step : next.config ∈ (state.config.step actual actualReady action).support) : False := by
    have same := ordered.ready_public_unique state.config.cut isPublic ready actualReady
    subst actual
    apply unfinished
    rw [state.config.step_cut event actualReady action next.config step]
    exact Finset.mem_insert_self _ _
  cases command with
  | grant query | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      rfl
  | executeSample query =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_executeSample_config_activated runtime state next query member
      · exact stutter.1
      · obtain ⟨actualReady, action, step, _⟩ := step
        exact (impossible query actualReady action step).elim
  | expire query =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_expire_config_activated runtime state next query member
      · exact stutter.1
      · obtain ⟨actualReady, action, step, _⟩ := step
        exact (impossible query actualReady action step).elim

/-- First-write memory preserves a cached action under every private command,
including arbitrary commands by the cache's owner. -/
theorem privateStep_remembered_of_some (state : State graph) (who : Player)
    (command : PrivateCommand graph) (event : graph.EventId) (action : graph.Action event)
    (cached : state.remembered event = some action) :
    (privateStep state who command).remembered event = some action := by
  cases command with
  | prepare serial raw => exact cached
  | remember query chosen =>
      by_cases owned : graph.actor? query = some who
      · rw [privateStep, dif_pos owned]
        cases memory : state.remembered query with
        | some prior => exact cached
        | none =>
            have different : event ≠ query := by
              intro same
              subst query
              rw [cached] at memory
              contradiction
            simpa only [Function.update_of_ne different] using cached
      · rw [privateStep, dif_neg owned]
        exact cached

private theorem privateStep_accepted (state : State graph) (who : Player)
    (command : PrivateCommand graph) :
    (privateStep state who command).accepted = state.accepted := by
  cases command with
  | prepare => rfl
  | remember event action =>
      simp only [privateStep]
      split
      · split <;> rfl
      · rfl

/-- Until a ready public event completes, every native action preserves its
semantic configuration, accepted handles, and any cached resolution action.
Private work on unrelated candidate slots and caches remains unrestricted. -/
theorem applicationStep_ready_public_frame (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (state next : runtime.application.State)
    (event : graph.EventId) (isPublic : (graph.outputLayout event).IsPublic)
    (ready : state.application.config.cut.Ready event)
    (unfinished : event ∉ next.application.config.cut.completed)
    (command : runtime.application.Action)
    (member : next ∈ (runtime.application.step state command).support) :
    next.application.config = state.application.config ∧
      next.application.accepted = state.application.accepted ∧
      ∀ action, state.application.remembered event = some action →
        next.application.remembered event = some action := by
  cases command with
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst next
      exact ⟨(privateStep_facts state.application who command).1,
        privateStep_accepted state.application who command,
        privateStep_remembered_of_some state.application who command event⟩
  | submit who packet | replay who id | deliver who id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst next
      exact ⟨rfl, rfl, fun _ cached => cached⟩
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst next
      cases found : state.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing state id found]
          exact ⟨rfl, rfl, fun _ cached => cached⟩
      | some message =>
          cases handled : runtime.handle state.application message with
          | none =>
              rw [runtime.application.includePending_reject state id message found handled]
              exact ⟨rfl, rfl, fun _ cached => cached⟩
          | some application =>
              rw [runtime.application.includePending_accept state id message application
                found handled] at unfinished
              exact (unfinished (runtime.handle_completes_ready_public ordered state.application
                application event isPublic ready message handled)).elim
  | environment command =>
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at member
      obtain ⟨application, supported, rfl⟩ := member
      refine ⟨environmentStep_config_of_ready_public_unfinished runtime ordered state.application
        application event isPublic ready unfinished command supported,
        (environmentStep_tables runtime state.application application command supported).1, ?_⟩
      intro action cached
      rw [environmentStep_remembered runtime state.application application command supported]
      exact cached

/-- A whole arbitrary native suffix cannot change a ready public event's
resolution inputs without completing that event. -/
theorem applicationRun_ready_public_frame (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (state next : runtime.application.State)
    (event : graph.EventId) (isPublic : (graph.outputLayout event).IsPublic)
    (ready : state.application.config.cut.Ready event)
    (unfinished : event ∉ next.application.config.cut.completed)
    (commands : List runtime.application.Action)
    (member : next ∈ (runtime.application.run commands state).support) :
    next.application.config = state.application.config ∧
      next.application.accepted = state.application.accepted ∧
      ∀ action, state.application.remembered event = some action →
        next.application.remembered event = some action := by
  induction commands generalizing state with
  | nil =>
      simp only [MessageApplication.run_nil, FinDist.mem_support_pure] at member
      subst next
      exact ⟨rfl, rfl, fun _ cached => cached⟩
  | cons command rest ih =>
      simp only [MessageApplication.run_cons, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, step, tail⟩ := member
      have intermediateUnfinished : event ∉ middle.application.config.cut.completed := by
        intro completed
        have later := runtime.application.run_application_invariant
          (fun application => event ∈ application.config.cut.completed)
          (fun application who command done =>
            privateStep_completed_subset application who command done)
          (fun application message after done accepted =>
            handle_completed_subset runtime application after message accepted done)
          (fun application command after done supported =>
            environmentStep_completed_subset runtime application after command supported done)
          middle next rest completed tail
        exact unfinished later
      have first := runtime.applicationStep_ready_public_frame ordered state middle event
        isPublic ready intermediateUnfinished command step
      have middleReady : middle.application.config.cut.Ready event := by
        simpa only [first.1] using ready
      have last := ih middle middleReady tail
      exact ⟨last.1.trans first.1, last.2.1.trans first.2.1,
        fun action cached => last.2.2 action (first.2.2 action cached)⟩

end Vegas.EventGraphRuntime
