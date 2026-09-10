/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyBindings
import Vegas.Compile.ApplicationBindingTimeouts

/-! # Timeout traffic and lifted source profiles

Binding and public-choice expiry are open protocol actions. The reference
lifting of a source behavioral profile never emits either: binding heads emit
only registration or opaque-binding commands, and voluntary choice heads use
codecs that reject expiry payloads. This fact does not restrict arbitrary
native policies.
-/

noncomputable section

namespace Vegas

variable {P : Type} {L : IExpr}

namespace ApplicationImage.Payload

/-- The two permissionless fallback requests added by timeout decoration. -/
def IsExpiry : ApplicationImage.Payload P L → Prop
  | .expireChoice _ | .expireBinding _ => True
  | _ => False

end ApplicationImage.Payload

namespace ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- No policy obtained by structurally lifting a source behavioral profile
submits either kind of permissionless fallback request. -/
theorem liftProfileIn_expiry_not_supported
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog) (player : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (payload : ApplicationImage.Payload P L) (hexpiry : payload.IsExpiry) :
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
              simp [ApplicationImage.Payload.IsExpiry] at hexpiry hbinding
        · simp at hcommand
  | publicChoice publicGuard next ih
  | conditional publicGuard next ih
  | conditionalCopy specification publicGuard next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterCommit.afterReveal player hcommand
      · split at hcommand
        · exact ChoiceController.not_supported_of_decode_none
            _ _ history view (.submit payload) (by simp)
            (by cases payload <;> first | exact False.elim hexpiry | rfl) hcommand
        · simp at hcommand

end ApplicationPlan

end Vegas

/-- info: 'Vegas.ApplicationPlan.liftProfileIn_expiry_not_supported' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.liftProfileIn_expiry_not_supported
