/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyBindings
import Vegas.Compile.ApplicationChoiceTimeouts

/-! # Timeout traffic and lifted source profiles

Public-choice expiry is an open protocol action.  The reference lifting of a
source behavioral profile never emits it: binding heads emit only registration
or binding commands, and voluntary choice heads use codecs that reject the
expiry payload.  This fact does not restrict arbitrary native policies.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- No policy obtained by structurally lifting a source behavioral profile
submits the public-choice expiry action. -/
theorem liftProfileIn_not_expireChoice_supported
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog) (player : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (address : Nat) :
    .submit (.expireChoice address) ∉
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
          · cases hbinding
        · simp at hcommand
  | publicChoice publicGuard next ih
  | conditional publicGuard next ih
  | conditionalCopy specification publicGuard next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterCommit.afterReveal player hcommand
      · split at hcommand
        · exact ChoiceController.not_supported_of_decode_none
            _ _ history view (.submit (.expireChoice address)) (by simp) rfl hcommand
        · simp at hcommand

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.liftProfileIn_not_expireChoice_supported' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.liftProfileIn_not_expireChoice_supported
