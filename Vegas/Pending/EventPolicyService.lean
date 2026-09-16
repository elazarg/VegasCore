/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicyCoherence
import Vegas.Pending.EventOpponentFrame

/-! # Prescribed policy coherence through adaptive event service

The owner policy may be interleaved with arbitrary opponent and environment
traffic.  This file lifts its local invocation invariant through the concrete
adaptive service interpreter.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Coherence depends only on the owner's authenticated history and the
remembered action at the event under consideration. -/
theorem PolicyCoherent.copy
    (runtime : EventGraphRuntime graph)
    (before after : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId)
    (coherent : PolicyCoherent runtime before owner event)
    (history : after.principalHistory owner = before.principalHistory owner)
    (remembered : after.native.application.remembered event =
      before.native.application.remembered event) :
    PolicyCoherent runtime after owner event := by
  refine ⟨coherent.actor, ?_, ?_, ?_, ?_⟩
  · simpa only [history] using coherent.stage_le
  · simpa only [history, remembered] using coherent.empty_iff
  · simpa only [history, remembered] using coherent.cached_of_stage
  · simpa only [history] using coherent.submitted_stage

/-- An arbitrary command by another player preserves every coherent event of
the prescribed owner. -/
theorem playerStep_other_policyCoherentAll
    (runtime : EventGraphRuntime graph)
    (execution next : runtime.application.PolicyExecution)
    (focal owner : Player) (different : owner ≠ focal)
    (command : Command runtime)
    (coherent : PolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.application.playerStep focal execution command).support) :
    PolicyCoherentAll runtime next owner := by
  intro event actor
  cases command with
  | privateCommand privateCommand =>
      rw [runtime.application.playerStep_private_eq] at supported
      simp only [FinDist.mem_support_pure] at supported
      subst next
      have frame := runtime.afterPrivate_opponent_event execution focal owner different
        event actor privateCommand
      exact (coherent event actor).copy runtime execution
        (runtime.application.afterPrivate execution focal privateCommand) owner event
        frame.1 frame.2.1
  | submit packet =>
      rw [runtime.application.playerStep_submit_eq] at supported
      simp only [FinDist.mem_support_pure] at supported
      subst next
      have frame := runtime.afterSubmit_opponent_event execution focal owner different event packet
      exact (coherent event actor).copy runtime execution
        (runtime.application.afterSubmit execution focal packet) owner event frame.1 frame.2.1
  | replay id =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at supported
      subst next
      apply (coherent event actor).copy runtime execution _ owner event
      · simp [different]
      · rfl
  | wait =>
      rw [runtime.application.playerStep_wait] at supported
      simp only [FinDist.mem_support_pure] at supported
      subst next
      apply (coherent event actor).copy runtime execution _ owner event
      · simp [different]
      · rfl

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

/-- Environment-policy execution preserves simultaneous owner coherence. -/
theorem environmentPolicyStep_policyCoherentAll
    (runtime : EventGraphRuntime graph)
    (execution next : runtime.application.PolicyExecution)
    (owner : Player) (command : runtime.application.EnvironmentPolicyCommand)
    (coherent : PolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    PolicyCoherentAll runtime next owner := by
  have histories := runtime.application.environmentStep_principalHistory execution command next
    supported
  have remembered := runtime.environmentPolicyStep_remembered execution next command supported
  intro event actor
  apply (coherent event actor).copy runtime execution next owner event
  · exact congrFun histories owner
  · exact congrFun remembered event

/-- The compiled owner invocation preserves coherence whether the current
public grant is present or absent. -/
theorem compilePlayerPolicy_invoke_policyCoherentAll_anyGrant
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (coherent : PolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.application.invoke players environment execution (.player owner)).support) :
    PolicyCoherentAll runtime next owner := by
  cases grant : execution.native.application.serviceGrant with
  | some event =>
      exact runtime.compilePlayerPolicy_invoke_policyCoherentAll owner policy players environment
        execution next event ownerCompiled grant coherent supported
  | none =>
      simp only [MessageApplication.invoke, ownerCompiled, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨command, commandMem, stepMem⟩ := supported
      have observedGrant :
          (MessageApplication.State.observe runtime.application execution.native
            owner).application.publicView.serviceGrant = none := by
        change execution.native.application.serviceGrant = none
        exact grant
      unfold compilePlayerPolicy at commandMem
      rw [observedGrant] at commandMem
      simp only [FinDist.mem_support_pure] at commandMem
      subst command
      rw [runtime.application.playerStep_wait] at stepMem
      simp only [FinDist.mem_support_pure] at stepMem
      subst next
      intro event actor
      exact (coherent event actor).afterWait runtime execution owner event

/-- Any actual player invocation preserves the prescribed owner's coherence:
the owner follows its compiled policy, while every other policy is arbitrary. -/
theorem playerInvoke_policyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (coherent : PolicyCoherentAll runtime execution owner)
    (who : Player)
    (supported : next ∈
      (runtime.application.invoke players environment execution (.player who)).support) :
    PolicyCoherentAll runtime next owner := by
  by_cases same : who = owner
  · subst who
    exact runtime.compilePlayerPolicy_invoke_policyCoherentAll_anyGrant owner policy players
      environment execution next ownerCompiled coherent supported
  · simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at supported
    obtain ⟨command, _, stepMem⟩ := supported
    exact runtime.playerStep_other_policyCoherentAll execution next who owner
      (Ne.symm same) command coherent stepMem

/-- One concrete service instruction preserves prescribed-owner coherence. -/
theorem serviceStep_policyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (coherent : PolicyCoherentAll runtime execution owner)
    (supported : next ∈ (runtime.serviceStep players wire instruction execution).support) :
    PolicyCoherentAll runtime next owner := by
  cases instruction with
  | player who =>
      exact runtime.playerInvoke_policyCoherentAll owner policy players
        (runtime.application.wireEnvironment wire) execution next ownerCompiled coherent who
        supported
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨command, _, stepMem⟩ := supported
      exact runtime.environmentPolicyStep_policyCoherentAll execution next owner command coherent
        stepMem
  | grant event | includeLatest event who | sample event | tick | expire event =>
      exact runtime.environmentPolicyStep_policyCoherentAll execution next owner _ coherent
        supported

/-- Every supported finite concrete service plan preserves prescribed-owner
coherence. -/
theorem runServicePlan_policyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (plan : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (coherent : PolicyCoherentAll runtime execution owner)
    (supported : next ∈ (runtime.runServicePlan players wire plan execution).support) :
    PolicyCoherentAll runtime next owner := by
  induction plan generalizing execution with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at supported
      subst next
      exact coherent
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, head, tail⟩ := supported
      exact ih middle
        (runtime.serviceStep_policyCoherentAll owner policy players wire instruction execution
          middle ownerCompiled coherent head) tail

theorem serviceEpoch_policyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (coherent : PolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.serviceEpoch roster reactionRounds players wire order execution).support) :
    PolicyCoherentAll runtime next owner := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨chosen, _, planMem⟩ := supported
  exact runtime.runServicePlan_policyCoherentAll owner policy players wire
    (epochPlan chosen roster reactionRounds) execution next ownerCompiled coherent planMem

/-- Any number of adaptive service epochs preserves prescribed-owner
coherence, with every other player policy unrestricted. -/
theorem runService_policyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (coherent : PolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.runService roster reactionRounds players wire order count execution).support) :
    PolicyCoherentAll runtime next owner := by
  induction count generalizing execution with
  | zero =>
      simp only [runService, FinDist.mem_support_pure] at supported
      subst next
      exact coherent
  | succ count ih =>
      simp only [runService, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, epochMem, tail⟩ := supported
      exact ih middle
        (serviceEpoch_policyCoherentAll runtime owner policy roster reactionRounds players wire
          order execution middle ownerCompiled coherent epochMem) tail

/-- The actual adaptive service initialized from an event input is coherent
for every prescribed owner at every supported final execution. -/
theorem runService_initial_policyCoherentAll
    (runtime : EventGraphRuntime graph) (input : graph.Inputs) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (supported : next ∈
      (runtime.runService roster reactionRounds players wire order count
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial input)))).support) :
    PolicyCoherentAll runtime next owner := by
  exact runtime.runService_policyCoherentAll owner policy roster reactionRounds players wire order
    count _ next ownerCompiled (runtime.policyCoherentAll_initial input owner) supported

end Vegas.EventGraphRuntime
