/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateKnowledge
import Interaction.SealedCandidatePolicyEmbedding
import Interaction.SealedResolutionKnowledge
import Interaction.MessageApplicationPolicyTrace

/-! # Policy-level candidate hiding

The execution relation retains the actual candidate-host player and
environment inputs. History retyping exposes the common compiled-policy
interface without discarding entries or granting access to private service
state. The release law uses the shared policy-trace interpreter.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

structure CandidateExecutionRelated (runtime : SealedResolution Principal Value)
    (known : CommitmentHandle Principal Nat → Prop)
    (left right : runtime.candidateApplication.PolicyExecution) : Prop where
  native : CandidateKnowledgeRelated runtime known left.native right.native
  histories : ∀ who, HistoryRelated runtime known who
    (runtime.registeredPlayerHistory (left.principalHistory who))
    (runtime.registeredPlayerHistory (right.principalHistory who))
  environmentHistory : left.environmentHistory = right.environmentHistory

variable {runtime : SealedResolution Principal Value}
variable {known : CommitmentHandle Principal Nat → Prop}
variable {left right : runtime.candidateApplication.PolicyExecution}

theorem CandidateExecutionRelated.initial : CandidateExecutionRelated runtime known
    (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))
    (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) :=
  ⟨CandidateKnowledgeRelated.initial, fun _ => List.Forall₂.nil, rfl⟩

theorem CandidateExecutionRelated.history_eq
    (related : CandidateExecutionRelated runtime known left right) (who : Principal)
    (hknown : ∀ slot, known (who, slot)) :
    left.principalHistory who = right.principalHistory who :=
  runtime.registeredPlayerHistory_injective ((related.histories who).eq hknown)

theorem CandidateExecutionRelated.playerStep
    (related : CandidateExecutionRelated runtime known left right)
    (who : Principal) (leftCommand rightCommand : runtime.candidateApplication.PlayerCommand)
    (hcommand : SealedProgram.CommandAgreement runtime.program known who leftCommand rightCommand)
    (hopening : ∀ payload, leftCommand = .submit payload →
      SealedProgram.OpeningKnown known ⟨(who, left.native.pool.nextSerial who), payload⟩)
    (nextLeft nextRight : runtime.candidateApplication.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.candidateApplication.playerStep who left leftCommand).support)
    (hright : nextRight ∈
      (runtime.candidateApplication.playerStep who right rightCommand).support) :
    CandidateExecutionRelated runtime known nextLeft nextRight := by
  refine ⟨?_, ?_, ?_⟩
  · have hl : nextLeft.native ∈
        ((runtime.candidateApplication.playerStep who left leftCommand).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨nextLeft, hleft, rfl⟩
    have hr : nextRight.native ∈
        ((runtime.candidateApplication.playerStep who right rightCommand).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨nextRight, hright, rfl⟩
    rw [MessageApplication.playerStep_native] at hl hr
    cases leftCommand with
    | privateCommand lc =>
        cases rightCommand with
        | privateCommand rc =>
            obtain ⟨hslot, hvalue⟩ := hcommand
            simp only [PlayerCommand.toAction, MessageApplication.step,
              FinDist.mem_support_pure] at hl hr
            rw [hl, hr]
            cases lc with
            | up lc =>
                cases rc with
                | up rc =>
                    obtain ⟨ls, lv⟩ := lc
                    obtain ⟨rs, rv⟩ := rc
                    dsimp only at hslot hvalue
                    subst rs
                    exact related.native.prepare who ls lv rv hvalue
        | submit | replay | wait => cases hcommand
    | submit payload =>
        cases rightCommand <;> cases hcommand
        simp only [PlayerCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at hl hr
        rw [hl, hr]
        exact related.native.submit who payload (hopening payload rfl)
    | replay id =>
        cases rightCommand <;> cases hcommand
        simp only [PlayerCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at hl hr
        rw [hl, hr]
        exact related.native.replay who id
    | wait =>
        cases rightCommand <;> cases hcommand
        simp only [PlayerCommand.toAction, FinDist.mem_support_pure] at hl hr
        rw [hl, hr]
        exact related.native
  · intro observer
    by_cases hwho : observer = who
    · subst observer
      rw [MessageApplication.playerStep_history_self _ who left leftCommand nextLeft hleft,
        MessageApplication.playerStep_history_self _ who right rightCommand nextRight hright]
      simp only [registeredPlayerHistory, List.map_append]
      exact List.rel_append (related.histories who)
        (List.Forall₂.cons
          ⟨congrArg runtime.registeredPlayerView (related.native.observe_eq who), hcommand⟩
          List.Forall₂.nil)
    · rw [MessageApplication.playerStep_other_history _ who observer hwho
        left leftCommand nextLeft hleft,
        MessageApplication.playerStep_other_history _ who observer hwho
        right rightCommand nextRight hright]
      exact related.histories observer
  · rw [MessageApplication.playerStep_environmentHistory _ who left leftCommand nextLeft hleft,
      MessageApplication.playerStep_environmentHistory _ who right rightCommand nextRight hright]
    exact related.environmentHistory

theorem CandidateExecutionRelated.environmentStep
    (related : CandidateExecutionRelated runtime known left right)
    (command : runtime.candidateApplication.EnvironmentPolicyCommand)
    (nextLeft nextRight : runtime.candidateApplication.PolicyExecution)
    (hleft : nextLeft ∈
      (runtime.candidateApplication.environmentPolicyStep left command).support)
    (hright : nextRight ∈
      (runtime.candidateApplication.environmentPolicyStep right command).support) :
    CandidateExecutionRelated runtime known nextLeft nextRight := by
  cases command <;>
    simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
      MessageApplication.step, candidateApplication, host, FinDist.pure_bind,
      FinDist.map_pure, FinDist.mem_support_pure] at hleft hright <;>
    subst nextLeft <;> subst nextRight
  all_goals
    refine ⟨?_, related.histories, ?_⟩
    rotate_left
    · have hv := related.native.environmentView_eq
      dsimp only [candidateApplication, host] at hv
      simp only [related.environmentHistory, hv]
  · exact related.native.deliver _ _
  · exact related.native.includePending _
  · exact related.native.tick
  · exact related.native



/-- Adaptive candidate-host policy execution preserves a permitted release
observation whenever the compiled commands respect its disclosure boundary.
There is no restriction to prepared candidate-player submissions. -/
theorem candidate_firstRelease_observation_law {Observation : Type*}
    (leftPlayers rightPlayers : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (release : runtime.candidateApplication.PolicyExecution → Bool)
    (observe : runtime.candidateApplication.PolicyExecution → Observation)
    (hrelease : ∀ left right, CandidateExecutionRelated runtime known left right →
      release left = release right)
    (hobserve : ∀ left right, CandidateExecutionRelated runtime known left right →
      observe left = observe right)
    (hplayers : ∀ left right, CandidateExecutionRelated runtime known left right →
      release left = false → ∀ who,
      ∃ commands : FinDist
          (runtime.candidateApplication.PlayerCommand × runtime.candidateApplication.PlayerCommand),
        leftPlayers who (left.principalHistory who)
            (State.observe runtime.candidateApplication left.native who) =
          commands.map Prod.fst ∧
        rightPlayers who (right.principalHistory who)
            (State.observe runtime.candidateApplication right.native who) =
          commands.map Prod.snd ∧
        ∀ pair ∈ commands.support,
          SealedProgram.CommandAgreement runtime.program known who pair.1 pair.2 ∧
          (∀ payload, pair.1 = .submit payload →
            SealedProgram.OpeningKnown known ⟨(who, left.native.pool.nextSerial who), payload⟩))
    (schedule : List (@Invocation Principal))
    (left right : runtime.candidateApplication.PolicyExecution)
    (related : CandidateExecutionRelated runtime known left right) :
    ((runtime.candidateApplication.tracePolicies leftPlayers environment schedule left).map
        (PolicyTrace.firstRelease release)).map observe =
      ((runtime.candidateApplication.tracePolicies rightPlayers environment schedule right).map
        (PolicyTrace.firstRelease release)).map observe := by
  apply runtime.candidateApplication.tracePolicies_firstRelease_of_steps
    leftPlayers rightPlayers environment (CandidateExecutionRelated runtime known) release observe
    hrelease hobserve
    (fun _ _ h => ⟨h.environmentHistory, h.native.environmentView_eq⟩)
    (fun _ _ h => h.environmentStep) ?_ schedule left right related
  intro left right related hstop who
  obtain ⟨commands, hleft, hright, hpairs⟩ := hplayers left right related hstop who
  refine ⟨commands, hleft, hright, ?_⟩
  intro pair hpair nextLeft nextRight hleftStep hrightStep
  obtain ⟨hcommand, hopening⟩ := hpairs pair hpair
  exact related.playerStep who pair.1 pair.2 hcommand hopening
    nextLeft nextRight hleftStep hrightStep

end Interaction.SealedResolution
