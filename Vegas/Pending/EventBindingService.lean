/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventBindingInvariant
import Vegas.Pending.EventService

/-! # Binding provenance through the adaptive event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem environmentPolicyStep_bindingInvariant
    (runtime : EventGraphRuntime graph)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (invariant : execution.native.application.BindingInvariant)
    (member : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    next.native.application.BindingInvariant := by
  have nativeMem : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, member, rfl⟩
  rw [runtime.application.environmentStep_native] at nativeMem
  cases actionEq : command.toAction with
  | none =>
      simp only [actionEq, FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]
      exact invariant
  | some action =>
      simp only [actionEq] at nativeMem
      exact applicationStep_bindingInvariant runtime execution.native next.native action
        invariant nativeMem

/-- Each concrete service instruction preserves binding provenance. -/
theorem serviceStep_bindingInvariant (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.BindingInvariant)
    (member : next ∈ (runtime.serviceStep players wire instruction execution).support) :
    next.native.application.BindingInvariant := by
  cases instruction with
  | player who =>
      obtain same | ⟨action, supported⟩ := runtime.application.invoke_native_step players
        (runtime.application.wireEnvironment wire) execution next (.player who) member
      · rw [same]
        exact invariant
      · exact applicationStep_bindingInvariant runtime execution.native next.native action
          invariant supported
  | wire =>
      obtain same | ⟨action, supported⟩ := runtime.application.invoke_native_step players
        (runtime.application.wireEnvironment wire) execution next .environment member
      · rw [same]
        exact invariant
      · exact applicationStep_bindingInvariant runtime execution.native next.native action
          invariant supported
  | grant event | includeLatest event owner | sample event | tick | expire event =>
      exact environmentPolicyStep_bindingInvariant runtime execution next _ invariant member

/-- A finite adaptive service plan preserves binding provenance. -/
theorem runServicePlan_bindingInvariant (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (plan : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.BindingInvariant)
    (member : next ∈ (runtime.runServicePlan players wire plan execution).support) :
    next.native.application.BindingInvariant := by
  induction plan generalizing execution with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst next
      exact invariant
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, head, tail⟩ := member
      exact ih middle
        (serviceStep_bindingInvariant runtime players wire instruction execution middle
          invariant head) tail

private theorem serviceEpoch_bindingInvariant (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.BindingInvariant)
    (member : next ∈ (runtime.serviceEpoch roster reactionRounds players wire order
      execution).support) : next.native.application.BindingInvariant := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at member
  obtain ⟨chosen, _, supported⟩ := member
  exact runServicePlan_bindingInvariant runtime players wire
    (epochPlan chosen roster reactionRounds) execution next invariant supported

/-- Any number of adaptive service epochs preserves binding provenance. -/
theorem runService_bindingInvariant (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (execution next : runtime.application.PolicyExecution)
    (invariant : execution.native.application.BindingInvariant)
    (member : next ∈ (runtime.runService roster reactionRounds players wire order count
      execution).support) : next.native.application.BindingInvariant := by
  induction count generalizing execution with
  | zero =>
      simp only [runService, FinDist.mem_support_pure] at member
      subst next
      exact invariant
  | succ count ih =>
      simp only [runService, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, epoch, tail⟩ := member
      exact ih middle
        (serviceEpoch_bindingInvariant runtime roster reactionRounds players wire order
          execution middle invariant epoch) tail

/-- Every outcome of the serviced event game retains exact binding provenance. -/
theorem servicedEventGame_bindingInvariant (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (next : runtime.application.PolicyExecution)
    (member : next ∈
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play players).support) :
    next.native.application.BindingInvariant := by
  simp only [servicedEventGame, FinDist.support_bind, Set.mem_iUnion] at member
  obtain ⟨input, _, supported⟩ := member
  exact runService_bindingInvariant runtime roster reactionRounds players wire order
    runtime.serviceEpochs _ next (State.initial_bindingInvariant input) supported

end Vegas.EventGraphRuntime
