/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateEmbedding
import Interaction.MessageApplicationPolicyInvariant

/-! # Prepared commitments throughout the actual policy runner

The invariant ties retained commitment packets to prior private preparations.
It covers pending messages, the ledger, inboxes, and sent histories, so delivery,
replay and arbitrary inclusion choices cannot bypass the preparation fact.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

structure PreparedExecution (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution) : Prop where
  memory : RegistrationMemory runtime execution
  accepted : AcceptedBinding runtime execution.native.application
  messages : execution.native.pool.Satisfies
    (SealedProgram.PreparedSubmission execution.native.application.service)

namespace PreparedExecution

variable {runtime : SealedResolution Principal Value}

theorem initial : PreparedExecution runtime
    (PolicyExecution.initial _ (State.initial _ runtime.initial)) :=
  ⟨RegistrationMemory.initial, AcceptedBinding.initial, MessagePool.Satisfies.empty⟩

theorem playerStep (execution next : runtime.messageApplication.PolicyExecution)
    (who : Principal) (command : runtime.messageApplication.PlayerCommand)
    (h : PreparedExecution runtime execution)
    (hsubmit : ∀ payload, command = .submit payload →
      SealedProgram.PreparedSubmission execution.native.application.service
        ⟨(who, execution.native.pool.nextSerial who), payload⟩)
    (hnext : next ∈ (runtime.messageApplication.playerStep who execution command).support) :
    PreparedExecution runtime next := by
  have hmemory := h.memory.playerStep execution next who command hnext
  cases command with
  | privateCommand command =>
      simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hmemory, h.accepted.register who command.down.1 command.down.2,
        h.messages.mono fun _ hmessage =>
          hmessage.sealValue who command.down.1 command.down.2⟩
  | submit payload =>
      simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hmemory, h.accepted, h.messages.submit who payload (hsubmit payload rfl)⟩
  | replay id =>
      simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hmemory, h.accepted, h.messages.replay who id⟩
  | wait =>
      simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
        FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hmemory, h.accepted, h.messages⟩

theorem environmentStep (execution next : runtime.messageApplication.PolicyExecution)
    (command : runtime.messageApplication.EnvironmentPolicyCommand)
    (h : PreparedExecution runtime execution)
    (hnext : next ∈ (runtime.messageApplication.environmentPolicyStep execution command).support) :
    PreparedExecution runtime next := by
  have hmemory := h.memory.environmentStep execution next command hnext
  have hpool := runtime.messageApplication.environmentPolicyStep_pool_satisfies
    _ execution next command h.messages hnext
  have hnative : next.native ∈
      ((runtime.messageApplication.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  refine ⟨hmemory, ?_, ?_⟩
  · cases command with
    | deliver observer id | wait =>
        simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact h.accepted
    | «include» id =>
        simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact runtime.messageApplication.includePending_application_invariant
          (AcceptedBinding runtime) (fun _ _ _ hbefore hafter => hbefore.handle _ hafter)
          execution.native id h.accepted
    | application command =>
        simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
          messageApplication, FinDist.map_pure, FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact h.accepted.tick
  · have hservice : next.native.application.service = execution.native.application.service := by
      cases command with
      | deliver observer id | wait =>
          simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
            FinDist.mem_support_pure] at hnative
          rw [hnative]
      | «include» id =>
          simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
            FinDist.mem_support_pure] at hnative
          rw [hnative]
          exact runtime.messageApplication.includePending_application_invariant
            (fun state => state.service = execution.native.application.service)
            (fun state message after hstate hafter =>
              (runtime.handle_service state after message hafter).trans hstate)
            execution.native id rfl
      | application command =>
          simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
            messageApplication, FinDist.map_pure, FinDist.mem_support_pure] at hnative
          rw [hnative]
          rfl
    rwa [hservice]

end PreparedExecution

/-- Local preparation discipline is sufficient for every actual retained
message to satisfy the candidate/registered handler agreement premise. The
environment is unrestricted; no liveness or incentive premise is needed. -/
theorem runPolicies_prepared
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (hsubmit : ∀ execution who payload,
      RegistrationMemory runtime execution →
      .submit payload ∈ (players who (execution.principalHistory who)
        (State.observe _ execution.native who)).support →
      ∀ serial, SealedProgram.PreparedSubmission execution.native.application.service
        ⟨(who, serial), payload⟩)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) : PreparedExecution runtime next := by
  apply runtime.messageApplication.runPolicies_execution_invariant (PreparedExecution runtime)
    players environment ?_ ?_ schedule execution next h hnext
  · intro current who command after hcurrent hcommand hafter
    apply hcurrent.playerStep current after who command ?_ hafter
    intro payload hpayload
    subst command
    exact hsubmit current who payload hcurrent.memory hcommand _
  · intro current command after hcurrent _ hafter
    exact hcurrent.environmentStep current after command hafter

end Interaction.SealedResolution
