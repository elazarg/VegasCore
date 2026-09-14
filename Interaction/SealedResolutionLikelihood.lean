/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.IdealCommitmentWeight
import Interaction.SealedResolutionPolicy
import Interaction.MessageApplicationTraceLikelihood

/-! # Exact native mass from first-registration factors

Player invocations contribute a factor only when they first fill a tracked
private slot. Submission, replay, delivery, inclusion, and clock advancement
leave the product unchanged. Local policy probabilities determine whether this
product is the mass of a queried trace; the theorem checks the remaining
whole-execution counting argument, including zero-probability traces.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable (runtime : SealedResolution Principal Value)

/-- The single factor introduced by this command's change to private storage.
The factor is one for occupied and untracked slots, regardless of payload. -/
def registrationFactor (handles : Finset (CommitmentHandle Principal Nat))
    (factor : CommitmentHandle Principal Nat → ℝ)
    (initial : runtime.messageApplication.PolicyExecution) (who : Principal) :
    runtime.messageApplication.PlayerCommand → ℝ
  | .privateCommand request =>
      if (who, request.down.1) ∈ handles ∧
          initial.native.application.service.lookup (who, request.down.1) = none
      then factor (who, request.down.1) else 1
  | .submit _ | .replay _ | .wait => 1

private theorem playerStep_registrationWeight
    (handles : Finset (CommitmentHandle Principal Nat))
    (factor : CommitmentHandle Principal Nat → ℝ)
    (initial next : runtime.messageApplication.PolicyExecution) (who : Principal)
    (command : runtime.messageApplication.PlayerCommand)
    (hnext : next ∈ (runtime.messageApplication.playerStep who initial command).support) :
    next.native.application.service.registrationWeight handles factor =
      initial.native.application.service.registrationWeight handles factor *
        runtime.registrationFactor handles factor initial who command := by
  cases command with
  | privateCommand request =>
      simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
        FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact initial.native.application.service.registrationWeight_sealValue handles factor
        who request.down.1 request.down.2
  | submit payload | replay id | wait =>
      simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
        FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact (mul_one _).symm

private theorem environmentStep_service
    (initial next : runtime.messageApplication.PolicyExecution)
    (command : runtime.messageApplication.EnvironmentPolicyCommand)
    (hnext : next ∈ (runtime.messageApplication.environmentPolicyStep initial command).support) :
    next.native.application.service = initial.native.application.service := by
  have hnative : next.native ∈
      ((runtime.messageApplication.environmentPolicyStep initial command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
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
        (fun state => state.service = initial.native.application.service)
        (fun state message after hstate hafter =>
          (runtime.handle_service state after message hafter).trans hstate) initial.native id rfl
  | application command =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step, messageApplication,
        FinDist.map_pure, FinDist.mem_support_pure] at hnative
      rw [hnative]
      rfl

private theorem environmentStep_pure
    (initial : runtime.messageApplication.PolicyExecution)
    (command : runtime.messageApplication.EnvironmentPolicyCommand) :
    ∃ next, runtime.messageApplication.environmentPolicyStep initial command =
      FinDist.pure next := by
  cases command <;>
    simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
      MessageApplication.step, messageApplication, FinDist.map_pure, FinDist.pure_bind] <;>
    exact ⟨_, rfl⟩

/-- Exact stopped-trace probability under the original players, expressed as
the product of fixed factors at occupied tracked handles. The reference law
only witnesses the queried execution. The local premise compares original
command probabilities at actual invocations, not at a chosen checkpoint.
The environment is deterministic but may inspect its entire declared view,
including pending messages. No fairness or positive-mass premise is used. -/
theorem tracePolicies_prefixThrough_prob_eq_registrationWeight
    (players reference : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : List runtime.messageApplication.EnvironmentEntry →
      EnvironmentObservation runtime.messageApplication →
      runtime.messageApplication.EnvironmentPolicyCommand)
    (release : runtime.messageApplication.PolicyExecution → Bool)
    (handles : Finset (CommitmentHandle Principal Nat))
    (factor : CommitmentHandle Principal Nat → ℝ)
    (schedule : List (@Invocation Principal)) (trace : runtime.messageApplication.PolicyTrace)
    (htrace : trace ∈ ((runtime.messageApplication.tracePolicies reference
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
        (PolicyTrace.prefixThrough release)).support)
    (hplayers : ∀ before initial who command next after,
      initial ∈ (runtime.messageApplication.runPolicies reference
        (fun history view => FinDist.pure (environment history view)) before
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).support →
      command ∈ (reference who (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).support →
      next ∈ (runtime.messageApplication.playerStep who initial command).support →
      trace.last ∈ (runtime.messageApplication.runPolicies reference
        (fun history view => FinDist.pure (environment history view)) after next).support →
      release initial = false →
      (players who (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).prob command =
          runtime.registrationFactor handles factor initial who command) :
    ((runtime.messageApplication.tracePolicies players
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
        (PolicyTrace.prefixThrough release)).prob trace =
      trace.last.native.application.service.registrationWeight handles factor := by
  have hmass := runtime.messageApplication.tracePolicies_prefixThrough_prob_mul players reference
    (fun history view => FinDist.pure (environment history view))
    (fun history view => FinDist.pure (environment history view)) release
    (fun execution => execution.native.application.service.registrationWeight handles factor)
    (PolicyExecution.initial _ (State.initial _ runtime.initial)) schedule trace htrace
  simp only [show (PolicyExecution.initial runtime.messageApplication
      (State.initial runtime.messageApplication runtime.initial)).native.application.service =
        IdealCommitments.empty from rfl, IdealCommitments.registrationWeight_empty,
    one_mul] at hmass
  apply hmass
  intro before initial invocation next after hbefore hnext hafter hrelease
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, hcommand, hstep⟩ := hnext
      rw [runtime.messageApplication.invoke_player_prob_of_step players _ who initial next
        command hstep, hplayers before initial who command next after hbefore hcommand hstep
          hafter hrelease]
      exact (runtime.playerStep_registrationWeight handles factor initial next who
        command hstep).symm
  | environment =>
      simp only [invoke, FinDist.pure_bind] at hnext ⊢
      obtain ⟨result, hresult⟩ := runtime.environmentStep_pure initial
        (environment initial.environmentHistory
          (State.environmentView runtime.messageApplication initial.native))
      have heq : next = result := FinDist.mem_support_pure.mp (hresult ▸ hnext)
      rw [hresult, ← heq, FinDist.prob_pure_self, mul_one,
        runtime.environmentStep_service initial next _ hnext]

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.tracePolicies_prefixThrough_prob_eq_registrationWeight'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.tracePolicies_prefixThrough_prob_eq_registrationWeight
