/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionKnowledge
import Interaction.MessageApplicationPolicyTrace

/-! # Lockstep policy execution under partial disclosure

The shared runner records actual native commands and observations. Public
commands agree; private registration values may differ at unknown handles.
The finite-run theorem consumes local policy agreement, so a compiler must
prove that agreement at each of its permitted disclosure points.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable {runtime : SealedResolution Principal Value}
variable {known : CommitmentHandle Principal Nat → Prop}
variable {left right : runtime.messageApplication.PolicyExecution}

theorem ExecutionRelated.initial : ExecutionRelated runtime known
    (PolicyExecution.initial _ (State.initial runtime.messageApplication runtime.initial))
    (PolicyExecution.initial _ (State.initial runtime.messageApplication runtime.initial)) :=
  ⟨KnowledgeRelated.initial, fun _ => List.Forall₂.nil, rfl,
    BeforeTimeoutBinding.initial, BeforeTimeoutBinding.initial⟩

theorem ExecutionRelated.playerStep (related : ExecutionRelated runtime known left right)
    (who : Principal) (leftCommand rightCommand : runtime.messageApplication.PlayerCommand)
    (hcommand : SealedProgram.CommandAgreement runtime.program known who leftCommand rightCommand)
    (hopening : ∀ payload, leftCommand = .submit payload →
      SealedProgram.OpeningKnown known ⟨(who, left.native.pool.nextSerial who), payload⟩)
    (nextLeft nextRight : runtime.messageApplication.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.messageApplication.playerStep who left leftCommand).support)
    (hright : nextRight ∈ (runtime.messageApplication.playerStep who right rightCommand).support) :
    ExecutionRelated runtime known nextLeft nextRight := by
  refine ⟨?_, ?_, ?_, related.bindingLeft.playerStep who leftCommand hleft,
    related.bindingRight.playerStep who rightCommand hright⟩
  · have hl : nextLeft.native ∈
        ((runtime.messageApplication.playerStep who left leftCommand).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨nextLeft, hleft, rfl⟩
    have hr : nextRight.native ∈
        ((runtime.messageApplication.playerStep who right rightCommand).map
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
                    exact related.native.register who ls lv rv hvalue
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
      exact List.rel_append (related.histories who)
        (List.Forall₂.cons ⟨related.native.observe_eq who, hcommand⟩ List.Forall₂.nil)
    · rw [MessageApplication.playerStep_other_history _ who observer hwho
        left leftCommand nextLeft hleft,
        MessageApplication.playerStep_other_history _ who observer hwho
        right rightCommand nextRight hright]
      exact related.histories observer
  · rw [MessageApplication.playerStep_environmentHistory _ who left leftCommand nextLeft hleft,
      MessageApplication.playerStep_environmentHistory _ who right rightCommand nextRight hright]
    exact related.environmentHistory

theorem ExecutionRelated.environmentStep
    (related : ExecutionRelated runtime known left right)
    (command : runtime.messageApplication.EnvironmentPolicyCommand)
    (nextLeft nextRight : runtime.messageApplication.PolicyExecution)
    (hleft : nextLeft ∈
      (runtime.messageApplication.environmentPolicyStep left command).support)
    (hright : nextRight ∈
      (runtime.messageApplication.environmentPolicyStep right command).support) :
    ExecutionRelated runtime known nextLeft nextRight := by
  have hbl := related.bindingLeft.environmentStep command hleft
  have hbr := related.bindingRight.environmentStep command hright
  cases command <;>
    simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
      MessageApplication.step, messageApplication, FinDist.pure_bind,
      FinDist.map_pure, FinDist.mem_support_pure] at hleft hright <;>
    subst nextLeft <;> subst nextRight
  all_goals
    refine ⟨?_, related.histories, ?_, hbl, hbr⟩
    rotate_left
    · have hv := related.native.environmentView_eq
      dsimp only [messageApplication] at hv
      simp only [related.environmentHistory, hv]
  · exact related.native.deliver _ _
  · exact related.native.includePending _
  · exact related.native.tick
  · exact related.native

private theorem playerStep_pure (who : Principal)
    (execution : runtime.messageApplication.PolicyExecution)
    (command : runtime.messageApplication.PlayerCommand) :
    ∃ next, runtime.messageApplication.playerStep who execution command = FinDist.pure next := by
  cases command <;>
    simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
      MessageApplication.step, FinDist.pure_bind] <;> exact ⟨_, rfl⟩

private theorem environmentStep_pure
    (execution : runtime.messageApplication.PolicyExecution)
    (command : runtime.messageApplication.EnvironmentPolicyCommand) :
    ∃ next, runtime.messageApplication.environmentPolicyStep execution command =
      FinDist.pure next := by
  cases command <;>
    simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
      MessageApplication.step, messageApplication, FinDist.map_pure,
      FinDist.pure_bind] <;> exact ⟨_, rfl⟩

/-- Local command agreement lifts to the law of the first selected snapshot.
The environment is arbitrary and may randomize using its full pool observation
and history. No agreement premise is imposed on play after the selected
snapshot. Policies and observations are those of the actual shared runner. -/
theorem firstRelease_observation_law {Observation : Type*}
    (leftPlayers rightPlayers : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (release : runtime.messageApplication.PolicyExecution → Bool)
    (observe : runtime.messageApplication.PolicyExecution → Observation)
    (hrelease : ∀ left right, ExecutionRelated runtime known left right →
      release left = release right)
    (hobserve : ∀ left right, ExecutionRelated runtime known left right →
      observe left = observe right)
    (hplayers : ∀ left right, ExecutionRelated runtime known left right →
      release left = false → ∀ who,
      ∃ commands : FinDist
          (runtime.messageApplication.PlayerCommand × runtime.messageApplication.PlayerCommand),
        leftPlayers who (left.principalHistory who)
            (State.observe runtime.messageApplication left.native who) =
          commands.map Prod.fst ∧
        rightPlayers who (right.principalHistory who)
            (State.observe runtime.messageApplication right.native who) =
          commands.map Prod.snd ∧
        ∀ pair ∈ commands.support,
          SealedProgram.CommandAgreement runtime.program known who pair.1 pair.2 ∧
          (∀ payload, pair.1 = .submit payload →
            SealedProgram.OpeningKnown known ⟨(who, left.native.pool.nextSerial who), payload⟩))
    (schedule : List (@Invocation Principal))
    (left right : runtime.messageApplication.PolicyExecution)
    (related : ExecutionRelated runtime known left right) :
    ((runtime.messageApplication.tracePolicies leftPlayers environment schedule left).map
        (PolicyTrace.firstRelease release)).map observe =
      ((runtime.messageApplication.tracePolicies rightPlayers environment schedule right).map
        (PolicyTrace.firstRelease release)).map observe := by
  induction schedule generalizing left right with
  | nil => simp only [tracePolicies, FinDist.map_pure, PolicyTrace.firstRelease,
      hobserve left right related]
  | cons invocation rest ih =>
      rw [tracePolicies_firstRelease_cons, tracePolicies_firstRelease_cons]
      have heq := hrelease left right related
      cases hl : release left with
      | true => simp only [← heq, hl, ↓reduceIte, FinDist.map_pure,
          hobserve left right related]
      | false =>
          simp only [← heq, hl, Bool.false_eq_true, ↓reduceIte, FinDist.map_bind]
          cases invocation with
          | player who =>
              obtain ⟨commands, hpl, hpr, hcommands⟩ := hplayers left right related hl who
              simp only [invoke, hpl, hpr, FinDist.bind_map, FinDist.bind_bind]
              apply FinDist.bind_congr
              intro pair hpair
              obtain ⟨lc, rc⟩ := pair
              obtain ⟨hc, hopen⟩ := hcommands (lc, rc) hpair
              obtain ⟨nl, hnl⟩ := playerStep_pure who left lc
              obtain ⟨nr, hnr⟩ := playerStep_pure who right rc
              simp only [hnl, hnr, FinDist.pure_bind]
              exact ih nl nr (related.playerStep who lc rc hc hopen nl nr
                (by rw [hnl, FinDist.mem_support_pure])
                (by rw [hnr, FinDist.mem_support_pure]))
          | environment =>
              simp only [invoke, FinDist.bind_bind, related.environmentHistory,
                related.native.environmentView_eq]
              apply FinDist.bind_congr
              intro command _
              obtain ⟨nl, hnl⟩ := environmentStep_pure left command
              obtain ⟨nr, hnr⟩ := environmentStep_pure right command
              simp only [hnl, hnr, FinDist.pure_bind]
              exact ih nl nr (related.environmentStep command nl nr
                (by rw [hnl, FinDist.mem_support_pure])
                (by rw [hnr, FinDist.mem_support_pure]))

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.firstRelease_observation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.firstRelease_observation_law
