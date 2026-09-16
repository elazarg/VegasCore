/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventHonestBlock
import Vegas.Pending.EventHonestResolution
import Vegas.Pending.EventHonestDeadline

/-! # Honest laws for complete asynchronous event service blocks -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem sample_completed (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy) (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution) (event : graph.EventId)
    (completed : event ∈ execution.native.application.config.cut.completed) :
    (runtime.serviceStep (runtime.compileProfile profile) wire (.sample event) execution).map
        (fun next => next.native.application.config) =
      FinDist.pure execution.native.application.config ∧
    ∀ next ∈ (runtime.serviceStep (runtime.compileProfile profile) wire
      (.sample event) execution).support, HonestBoundary runtime inputs next := by
  constructor
  · have projected := congrArg (fun law : FinDist runtime.application.State =>
        law.map (fun native => native.application.config))
      (runtime.application.environmentStep_native execution (.application (.executeSample event)))
    simp only [FinDist.map_comp, Function.comp_def] at projected
    change (runtime.application.environmentPolicyStep execution
      (.application (.executeSample event))).map (fun next => next.native.application.config) = _
    rw [projected]
    simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step]
    change ((environmentStep runtime execution.native.application (.executeSample event)).map
      (fun application => ({ execution.native with application } : runtime.application.State))).map
        (fun native => native.application.config) = _
    rw [environmentStep_executeSample_of_not_ready runtime execution.native.application event
      (fun ready => ready.1 completed), FinDist.map_pure, FinDist.map_pure]
  · intro next member
    exact environmentPolicyStep_honestBoundary runtime inputs execution next
      (.executeSample event) boundary member

private theorem append_sample (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy) (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (ready : execution.native.application.config.cut.Ready event)
    (plan : List (ServiceInstruction graph))
    (configLaw : (runtime.runServicePlan (runtime.compileProfile profile) wire plan execution).map
      (fun next => next.native.application.config) =
        graph.normalizedPolicyStep profile execution.native.application.config event ready)
    (boundaryLaw : ∀ next ∈
      (runtime.runServicePlan (runtime.compileProfile profile) wire plan execution).support,
        HonestBoundary runtime inputs next) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
      (plan ++ [.sample event]) execution).map (fun next => next.native.application.config) =
        graph.normalizedPolicyStep profile execution.native.application.config event ready ∧
    ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
      (plan ++ [.sample event]) execution).support, HonestBoundary runtime inputs next := by
  have middleCompleted middle (member : middle ∈
      (runtime.runServicePlan (runtime.compileProfile profile) wire plan execution).support) :
      event ∈ middle.native.application.config.cut.completed := by
    have supported : middle.native.application.config ∈
        (graph.normalizedPolicyStep profile
          execution.native.application.config event ready).support := by
      rw [← configLaw, FinDist.support_map]
      exact ⟨middle, member, rfl⟩
    rw [graph.normalizedPolicyStep_cut profile _ event ready _ supported]
    exact Finset.mem_insert_self _ _
  rw [runtime.runServicePlan_append]
  simp only [runServicePlan, FinDist.bind_pure]
  constructor
  · rw [FinDist.map_bind]
    calc
      _ = (runtime.runServicePlan (runtime.compileProfile profile) wire plan execution).bind
          (fun next => FinDist.pure next.native.application.config) := by
        apply FinDist.bind_congr
        intro next member
        exact (sample_completed runtime inputs profile wire next
          (boundaryLaw next member) event (middleCompleted next member)).1
      _ = _ := by rw [← FinDist.map_eq_bind]; exact configLaw
  · intro next member
    rw [FinDist.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨middle, head, tail⟩ := member
    exact (sample_completed runtime inputs profile wire middle
      (boundaryLaw middle head) event (middleCompleted middle head)).2 next tail

omit [DecidableEq Player] in
private theorem actor_cast (event : graph.EventId) (output : EventField Player L)
    (same : graph.outputLayout event = output) :
    EventCode.actor (cast (congrArg (EventCode graph.layout) same) (graph.nodes event)) =
      graph.actor? event := by
  cases same
  rfl

/-- Every ready event block implements its graph kernel, for the actual
adaptive wire and prescribed player policies, and restores the honest boundary. -/
theorem HonestBoundary.ready_event_block (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (feasible : runtime.ServiceFeasible)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (roster : List Player) (reactionRounds : Nat)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (age : execution.native.application.ActivationAgeOne)
    (event : graph.EventId) (ready : execution.native.application.config.cut.Ready event) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
      (eventServicePlan roster reactionRounds event) execution).map
        (fun next => next.native.application.config) =
      graph.normalizedPolicyStep profile execution.native.application.config event ready ∧
    ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
      (eventServicePlan roster reactionRounds event) execution).support,
      HonestBoundary runtime inputs next := by
  have timely (owner) (actor : graph.actor? event = some owner) :
      execution.native.application.WithinDeadline runtime event := by
    obtain ⟨entered, activated⟩ := boundary.invariant.activatedAt_eq_some_of_ready_actor
      event ready (by simp [actor])
    exact age.withinDeadline runtime feasible event entered activated ready.1
  cases viewNode : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      have actor : graph.actor? event = some owner := by
        have same := congrArg EventCode.actor codeEq
        rwa [actor_cast event _ outputEq] at same
      have plan : eventServicePlan roster reactionRounds event =
          .grant event ::
            ((List.replicate 3 (.player owner) ++
              (List.replicate reactionRounds (.wire :: roster.map .player)).flatten ++
              [.includeLatest event owner]) ++ [.sample event]) := by
        simp [eventServicePlan, actor]
      rw [plan, runServicePlan, runtime.serviceStep_grant_eq, FinDist.pure_bind]
      apply append_sample runtime inputs profile wire (runtime.afterGrant execution event)
        event ready
      · exact (boundary.afterGrant event).bind_ownerBlock_reactions_law runtime inputs
          profile wire roster reactionRounds _ event owner payload outputEq codeEq viewNode
          rfl ready (timely owner actor) actor
      · exact (boundary.afterGrant event).bind_ownerBlock_reactions_boundary runtime inputs
          profile wire roster reactionRounds _ event owner payload outputEq codeEq viewNode
          rfl ready (timely owner actor) actor
  | resolve owner payload binding checks outputEq codeEq =>
      have actor : graph.actor? event = some owner := by
        have same := congrArg EventCode.actor codeEq
        rwa [actor_cast event _ outputEq] at same
      have plan : eventServicePlan roster reactionRounds event =
          .grant event ::
            ((List.replicate 3 (.player owner) ++
              ((List.replicate reactionRounds (.wire :: roster.map .player)).flatten ++
                [.includeLatest event owner])) ++ [.sample event]) := by
        simp [eventServicePlan, actor]
      rw [plan, runServicePlan, runtime.serviceStep_grant_eq, FinDist.pure_bind]
      have block := (boundary.afterGrant event).resolve_reacted_block runtime inputs profile
        wire _ event owner payload binding checks outputEq codeEq viewNode rfl ready
        (timely owner actor) actor _ (honestReactionPlan_allowed roster reactionRounds)
      exact append_sample runtime inputs profile wire (runtime.afterGrant execution event)
        event ready _ block.1 block.2
  | sample payload law outputEq codeEq =>
      have ownerless : graph.actor? event = none := by
        have same := congrArg EventCode.actor codeEq
        rwa [actor_cast event _ outputEq] at same
      exact boundary.sample_block runtime inputs profile wire roster reactionRounds execution
        event ready ownerless payload law outputEq codeEq viewNode

end Vegas.EventGraphRuntime
