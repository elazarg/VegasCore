/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventReplayEnvironment
import Vegas.Pending.EventServiceCompletion

/-! # Epoch positions of reachable service controls

Every small-step prefix consists of complete adaptive epochs followed by a
prefix of one selected epoch plan. This representation retains the actual
order-policy support, rather than allowing arbitrary instruction sequences.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}
variable (runtime : EventGraphRuntime graph)
variable (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
variable (players : Player → runtime.application.PlayerPolicy)
variable (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)

/-- An execution reached after a finite number of complete adaptive epochs. -/
def EpochBoundary (execution : runtime.application.PolicyExecution) : Prop :=
  ∃ input ∈ inputs.support, ∃ count,
    execution ∈ (runtime.runService roster reactionRounds players wire order count
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial input)))).support

theorem EpochBoundary.after_epoch
    {before after : runtime.application.PolicyExecution}
    (boundary : EpochBoundary runtime inputs roster reactionRounds players wire order before)
    (member : after ∈
      (runtime.serviceEpoch roster reactionRounds players wire order before).support) :
    EpochBoundary runtime inputs roster reactionRounds players wire order after := by
  obtain ⟨input, inputMem, count, beforeMem⟩ := boundary
  refine ⟨input, inputMem, count + 1, ?_⟩
  rw [runtime.runService_add, FinDist.support_bind]
  simp only [Set.mem_iUnion]
  refine ⟨before, beforeMem, ?_⟩
  simpa only [runService, FinDist.bind_pure] using member

/-- A boundary or a supported prefix of an actual selected epoch. The
remaining epoch count is immaterial to prefix invariants. -/
def ServicePosition (control : ServiceControl runtime) : Prop :=
  (control.plan = [] ∧
    EpochBoundary runtime inputs roster reactionRounds players wire order control.execution) ∨
  ∃ (boundary : runtime.application.PolicyExecution) (chosen : ServiceOrder graph)
      (executed : List (ServiceInstruction graph)),
    EpochBoundary runtime inputs roster reactionRounds players wire order boundary ∧
    chosen ∈ (order boundary.environmentHistory
      (MessageApplication.State.environmentView runtime.application boundary.native)).support ∧
    epochPlan chosen roster reactionRounds = executed ++ control.plan ∧
    control.execution ∈ (runtime.runServicePlan players wire executed boundary).support

/-- Consuming the whole selected plan reaches the next genuine epoch
boundary, even before the next small-step order selection occurs. -/
theorem ServicePosition.boundary_of_empty {control : ServiceControl runtime}
    (position : ServicePosition runtime inputs roster reactionRounds players wire order control)
    (empty : control.plan = []) :
    EpochBoundary runtime inputs roster reactionRounds players wire order control.execution := by
  rcases position with ⟨_, boundary⟩ | ⟨before, chosen, executed, boundary, chosenMem, plan, run⟩
  · exact boundary
  · have planEq : epochPlan chosen roster reactionRounds = executed := by
      simpa only [empty, List.append_nil] using plan
    apply boundary.after_epoch runtime inputs roster reactionRounds players wire order
    simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨chosen, chosenMem, by simpa only [planEq] using run⟩

theorem ServiceReachable.position {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control) :
    ServicePosition runtime inputs roster reactionRounds players wire order control := by
  induction reachable with
  | initial input member =>
      exact Or.inl ⟨rfl, input, member, 0, by simp [runService]⟩
  | @step before after prior supported ih =>
      rcases runtime.serviceControlStep_cases roster reactionRounds players wire order
        before after supported with same | selected | executed
      · obtain ⟨_, _, rfl⟩ := same
        exact ih
      · obtain ⟨epochs, chosen, empty, _, chosenMem, rfl⟩ := selected
        have boundary := ih.boundary_of_empty runtime inputs roster reactionRounds players
          wire order empty
        exact Or.inr ⟨before.execution, chosen, [], boundary, chosenMem, rfl,
          by simp [runServicePlan]⟩
      · obtain ⟨instruction, rest, planEq, _, tailEq, member⟩ := executed
        rcases ih with ⟨empty, _⟩ | ⟨boundary, chosen, prefixPlan, priorBoundary,
            chosenMem, splitPlan, prefixMem⟩
        · simp [planEq] at empty
        · refine Or.inr ⟨boundary, chosen, prefixPlan ++ [instruction], priorBoundary,
            chosenMem, ?_, ?_⟩
          · rw [splitPlan, planEq, tailEq, List.append_assoc]
            rfl
          · rw [runtime.runServicePlan_append, FinDist.support_bind]
            simp only [Set.mem_iUnion]
            refine ⟨before.execution, prefixMem, ?_⟩
            simpa only [runServicePlan, FinDist.bind_pure] using member

end Vegas.EventGraphRuntime
