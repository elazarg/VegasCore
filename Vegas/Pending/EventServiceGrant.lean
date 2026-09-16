/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicyBlock
import Vegas.Pending.EventServiceLaw

/-! # Public grant frames through native event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

theorem playerStep_serviceGrant (runtime : EventGraphRuntime graph)
    (owner : Player) (before after : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (member : after ∈ (runtime.application.playerStep owner before command).support) :
    after.native.application.serviceGrant = before.native.application.serviceGrant := by
  cases command with
  | privateCommand command =>
      rw [runtime.application.playerStep_private_eq, FinDist.mem_support_pure] at member
      subst after
      exact runtime.afterPrivate_serviceGrant before owner command
  | submit payload =>
      rw [runtime.application.playerStep_submit_eq, FinDist.mem_support_pure] at member
      subst after
      rfl
  | replay id | wait =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at member
      subst after
      rfl

/-- Packet delivery and inclusion cannot change the service grant. An
application command changes it only when that command explicitly grants. -/
theorem environmentPolicyStep_serviceGrant (runtime : EventGraphRuntime graph)
    (before after : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (noGrant : ∀ event, command ≠ .application (.grant event))
    (member : after ∈ (runtime.application.environmentPolicyStep before command).support) :
    after.native.application.serviceGrant = before.native.application.serviceGrant := by
  have native : after.native ∈
      ((runtime.application.environmentPolicyStep before command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨after, member, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  cases command with
  | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        FinDist.mem_support_pure] at native
      rw [native]
  | deliver owner id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
      cases lookup : before.native.pool.lookup id with
      | none => rw [runtime.application.includePending_missing before.native id lookup]
      | some message =>
          cases accepted : runtime.handle before.native.application message with
          | none =>
              rw [runtime.application.includePending_reject before.native id message
                lookup accepted]
          | some next =>
              rw [runtime.application.includePending_accept before.native id message next
                lookup accepted]
              exact runtime.handle_serviceGrant before.native.application next message accepted
  | application command =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.support_map, Set.mem_image] at native
      obtain ⟨state, stateMem, nativeEq⟩ := native
      rw [← nativeEq]
      have granted := environmentStep_serviceGrant runtime before.native.application state
        command stateMem
      cases command with
      | grant event => exact (noGrant event rfl).elim
      | executeSample event | advanceClock | expire event => exact granted

/-- A service instruction preserves the current grant unless it is itself
a grant instruction. Player and wire policies remain unrestricted. -/
theorem serviceStep_serviceGrant_eq (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (noGrant : ∀ event, instruction ≠ .grant event)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    after.native.application.serviceGrant = before.native.application.serviceGrant := by
  cases instruction with
  | player owner =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact runtime.playerStep_serviceGrant owner before after command step
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      apply runtime.environmentPolicyStep_serviceGrant before after
        (WireCommand.toEnvironmentCommand runtime.application command) _ step
      intro event
      cases command <;> simp [WireCommand.toEnvironmentCommand]
  | grant event => exact (noGrant event rfl).elim
  | includeLatest event owner =>
      apply runtime.environmentPolicyStep_serviceGrant before after _ _ member
      intro query
      unfold latestEventSubmissionCommand
      split <;> simp
  | sample event | tick | expire event =>
      apply runtime.environmentPolicyStep_serviceGrant before after _ _ member
      intro query
      simp

/-- An entire grant-free service tail retains the announced event. -/
theorem runServicePlan_serviceGrant_eq (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (noGrant : ∀ instruction ∈ plan, ∀ event, instruction ≠ .grant event)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    after.native.application.serviceGrant = before.native.application.serviceGrant := by
  induction plan generalizing before with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst after
      rfl
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, first, tail⟩ := member
      exact (ih middle (fun next mem => noGrant next (List.mem_cons_of_mem _ mem)) tail).trans
        (runtime.serviceStep_serviceGrant_eq players wire instruction before middle
          (noGrant instruction List.mem_cons_self) first)

end Vegas.EventGraphRuntime
