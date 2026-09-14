/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidateWeight
import Interaction.SealedCandidateProvenance
import Interaction.MessageApplicationTraceLikelihood

/-! # Exact native mass from candidate preparation factors

Fresh preparation introduces one factor at its tracked owner/handle. Acceptance
may fix an unopenable candidate but preserves the product. The shared stopped
trace likelihood theorem counts these factors under arbitrary fixed environment
responses; no fairness or positive-mass assumption is needed.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable (runtime : SealedResolution Principal Value)

/-- The probability factor introduced by a fresh tracked preparation. -/
def candidatePreparationFactor (handles : Finset (CommitmentHandle Principal Nat))
    (factor : CommitmentHandle Principal Nat → ℝ)
    (initial : runtime.candidateApplication.PolicyExecution) (who : Principal) :
    runtime.candidateApplication.PlayerCommand → ℝ
  | .privateCommand request =>
      if (who, request.down.1) ∈ handles ∧
          initial.native.application.service.lookup (who, request.down.1) = .fresh
      then factor (who, request.down.1) else 1
  | .submit _ | .replay _ | .wait => 1

private theorem playerStep_preparationWeight
    (handles : Finset (CommitmentHandle Principal Nat))
    (factor : CommitmentHandle Principal Nat → ℝ)
    (initial next : runtime.candidateApplication.PolicyExecution) (who : Principal)
    (command : runtime.candidateApplication.PlayerCommand)
    (hnext : next ∈ (runtime.candidateApplication.playerStep who initial command).support) :
    next.native.application.service.preparationWeight handles factor =
      initial.native.application.service.preparationWeight handles factor *
        runtime.candidatePreparationFactor handles factor initial who command := by
  cases command with
  | privateCommand request =>
      simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
        FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact initial.native.application.service.preparationWeight_prepare handles factor
        who request.down.1 request.down.2
  | submit payload | replay id | wait =>
      simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
        FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact (mul_one _).symm

private theorem candidateHandle_preparationWeight
    (handles : Finset (CommitmentHandle Principal Nat))
    (factor : CommitmentHandle Principal Nat → ℝ)
    (initial next : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.candidateHandle initial message = some next) :
    next.service.preparationWeight handles factor =
      initial.service.preparationWeight handles factor := by
  unfold candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge initial.visible.timeouts).candidateMessage?
        initial.service initial.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
        subst next
        rcases (runtime.program.discharge initial.visible.timeouts).candidateMessage?_effect
            initial.service initial.visible.events message result hmessage with
          ⟨node, selected, _hp, rfl⟩ | ⟨node, selected, claimed, _hp, rfl⟩
        · exact initial.service.preparationWeight_accept handles factor selected
        · rfl

private theorem environmentStep_preparationWeight
    (handles : Finset (CommitmentHandle Principal Nat))
    (factor : CommitmentHandle Principal Nat → ℝ)
    (initial next : runtime.candidateApplication.PolicyExecution)
    (command : runtime.candidateApplication.EnvironmentPolicyCommand)
    (hnext : next ∈ (runtime.candidateApplication.environmentPolicyStep initial command).support) :
    next.native.application.service.preparationWeight handles factor =
      initial.native.application.service.preparationWeight handles factor := by
  have hnative : next.native ∈
      ((runtime.candidateApplication.environmentPolicyStep initial command).map
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
      exact runtime.candidateApplication.includePending_application_invariant
        (fun state => state.service.preparationWeight handles factor =
          initial.native.application.service.preparationWeight handles factor)
        (fun state message after hstate hafter =>
          (runtime.candidateHandle_preparationWeight handles factor
            state after message hafter).trans hstate) initial.native id rfl
  | application command =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step, candidateApplication,
        host, FinDist.map_pure, FinDist.mem_support_pure] at hnative
      rw [hnative]
      rfl

private theorem candidateEnvironmentStep_pure
    (initial : runtime.candidateApplication.PolicyExecution)
    (command : runtime.candidateApplication.EnvironmentPolicyCommand) :
    ∃ next, runtime.candidateApplication.environmentPolicyStep initial command =
      FinDist.pure next := by
  cases command <;>
    simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
      MessageApplication.step, candidateApplication, host, FinDist.map_pure, FinDist.pure_bind] <;>
    exact ⟨_, rfl⟩

/-- Exact original stopped-trace mass under local preparation probabilities.
The reference law supplies the queried execution, without requiring that it
have positive original mass. The environment may inspect pending messages. -/
theorem tracePolicies_prefixThrough_prob_eq_preparationWeight
    (players reference : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : List runtime.candidateApplication.EnvironmentEntry →
      EnvironmentObservation runtime.candidateApplication →
      runtime.candidateApplication.EnvironmentPolicyCommand)
    (release : runtime.candidateApplication.PolicyExecution → Bool)
    (handles : Finset (CommitmentHandle Principal Nat))
    (factor : CommitmentHandle Principal Nat → ℝ)
    (schedule : List (@Invocation Principal)) (trace : runtime.candidateApplication.PolicyTrace)
    (htrace : trace ∈ ((runtime.candidateApplication.tracePolicies reference
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
        (PolicyTrace.prefixThrough release)).support)
    (hplayers : ∀ before initial who command next after,
      initial ∈ (runtime.candidateApplication.runPolicies reference
        (fun history view => FinDist.pure (environment history view)) before
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support →
      command ∈ (reference who (initial.principalHistory who)
        (State.observe runtime.candidateApplication initial.native who)).support →
      next ∈ (runtime.candidateApplication.playerStep who initial command).support →
      trace.last ∈ (runtime.candidateApplication.runPolicies reference
        (fun history view => FinDist.pure (environment history view)) after next).support →
      release initial = false →
      (players who (initial.principalHistory who)
        (State.observe runtime.candidateApplication initial.native who)).prob command =
          runtime.candidatePreparationFactor handles factor initial who command) :
    ((runtime.candidateApplication.tracePolicies players
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
        (PolicyTrace.prefixThrough release)).prob trace =
      trace.last.native.application.service.preparationWeight handles factor := by
  have hmass := runtime.candidateApplication.tracePolicies_prefixThrough_prob_mul players reference
    (fun history view => FinDist.pure (environment history view))
    (fun history view => FinDist.pure (environment history view)) release
    (fun execution => execution.native.application.service.preparationWeight handles factor)
    (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) schedule trace htrace
  simp only [show (PolicyExecution.initial runtime.candidateApplication
      (State.initial runtime.candidateApplication
        runtime.candidateInitial)).native.application.service = CommitmentCandidates.empty from rfl,
    CommitmentCandidates.preparationWeight_empty,
    one_mul] at hmass
  apply hmass
  intro before initial invocation next after hbefore hnext hafter hrelease
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, hcommand, hstep⟩ := hnext
      rw [runtime.candidateApplication.invoke_player_prob_of_step players _ who initial next
        command hstep, hplayers before initial who command next after hbefore hcommand hstep
          hafter hrelease]
      exact (runtime.playerStep_preparationWeight handles factor initial next who
        command hstep).symm
  | environment =>
      simp only [invoke, FinDist.pure_bind] at hnext ⊢
      obtain ⟨result, hresult⟩ := runtime.candidateEnvironmentStep_pure initial
        (environment initial.environmentHistory
          (State.environmentView runtime.candidateApplication initial.native))
      have heq : next = result := FinDist.mem_support_pure.mp (hresult ▸ hnext)
      rw [hresult, ← heq, FinDist.prob_pure_self, mul_one,
        runtime.environmentStep_preparationWeight handles factor initial next _ hnext]

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.tracePolicies_prefixThrough_prob_eq_preparationWeight'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.tracePolicies_prefixThrough_prob_eq_preparationWeight
