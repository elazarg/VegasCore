/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.ApplicationDeadlineIndependence
import Vegas.Compile.ApplicationPolicy

/-! # Deadline-independent generated reference policies

Policies obtained by lifting a source profile never submit any of the three
payload forms whose handler result depends on an absolute deadline. This is a
property of the reference lift, not a restriction on runtime strategies.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem liftProfileIn_deadlineDependent_not_supported
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog) (player : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (payload : ApplicationImage.Payload P L) (hdependent : ¬payload.DeadlineIndependent) :
    .submit payload ∉
      (plan.liftProfileIn image deadlineOf profile player history view).support := by
  intro hcommand
  induction plan generalizing player with
  | ret => simp [liftProfileIn] at hcommand
  | sample next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterSample player hcommand
      · simp at hcommand
  | binding unrestricted next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterCommit player hcommand
      · split at hcommand
        · rename_i howner
          subst player
          rcases SourceDecisionSite.bindingPolicy_supported_command
              _ _ _ _ _ _ _ _ hcommand with hwait | hregister | hbinding
          · cases hwait
          · obtain ⟨value, hvalue⟩ := hregister
            cases hvalue
          · cases payload <;>
              simp [ApplicationImage.Payload.DeadlineIndependent] at hdependent hbinding
        · simp at hcommand
  | publicChoice publicGuard next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterCommit.afterReveal player hcommand
      · split at hcommand
        · apply ChoiceController.not_supported_of_decode_none
            _ _ history view (.submit payload) (by simp) _ hcommand
          cases payload with
          | choice address value => exact False.elim (hdependent trivial)
          | expireChoice address => rfl
          | binding address handle => exact False.elim (hdependent trivial)
          | expireBinding address => rfl
          | conditional address request => rfl
          | malformed data => exact False.elim (hdependent trivial)
        · simp at hcommand
  | conditional publicGuard next ih
  | conditionalCopy specification publicGuard next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterCommit.afterReveal player hcommand
      · split at hcommand
        · simp only [ConditionalPublicationSite.imagePolicy] at hcommand
          split at hcommand
          · simp at hcommand
          · rename_i disposition _hbinding
            cases disposition <;>
              apply ChoiceController.not_supported_of_decode_none
                _ _ history view (.submit payload) (by simp) _ hcommand <;>
              cases payload with
              | choice address value => exact False.elim (hdependent trivial)
              | expireChoice address => rfl
              | binding address handle => exact False.elim (hdependent trivial)
              | expireBinding address => rfl
              | malformed data => exact False.elim (hdependent trivial)
              | conditional address request =>
                cases request with
                | opening handle value | decline | cleartext value | malformed =>
                    exact False.elim (hdependent trivial)
                | expire =>
                    simp [ConditionalPublicationSite.imageController,
                      ConditionalPublicationSite.controllerFor,
                      ConditionalPublicationSite.choiceEncodingFor,
                      ChoiceEncoding.submission, ChoiceEncoding.trans,
                      ChoiceEncoding.reindex, ChoiceEncoding.atEndpoint,
                      ApplicationImage.conditionalTransport,
                      ConditionalPublication.addressedChoiceEncoding,
                      ConditionalPublication.addressedDefaultChoiceEncoding]
        · simp at hcommand

/-- Every supported submission of the structural source-profile lift is
independent of all emitted absolute deadlines. -/
theorem liftProfileIn_deadlineIndependent
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog) (player : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (payload : ApplicationImage.Payload P L)
    (hsubmit : .submit payload ∈
      (plan.liftProfileIn image deadlineOf profile player history view).support) :
    payload.DeadlineIndependent := by
  by_contra hdependent
  exact plan.liftProfileIn_deadlineDependent_not_supported image deadlineOf profile player
    history view payload hdependent hsubmit

/-- Specialization to the complete plan's generated image. -/
theorem liftProfile_deadlineIndependent
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (profile : SourceBehavioralProfile prog) (player : P)
    (history : List (plan.image deadlineOf).application.PlayerEntry)
    (view : (plan.image deadlineOf).application.View)
    (payload : ApplicationImage.Payload P L)
    (hsubmit : .submit payload ∈
      (plan.liftProfile deadlineOf profile player history view).support) :
    payload.DeadlineIndependent :=
  plan.liftProfileIn_deadlineIndependent (plan.image deadlineOf) deadlineOf profile player
    history view payload hsubmit

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.liftProfileIn_deadlineIndependent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.liftProfileIn_deadlineIndependent

/-- info: 'Vegas.ApplicationPlan.liftProfile_deadlineIndependent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.liftProfile_deadlineIndependent
