/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PolicyHistory

/-! # Composition of typed graph-policy restrictions -/

noncomputable section
namespace Vegas.GraphRuntime.Prefix

open Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- A fixed typed cursor has only one prefix witness. In particular policy
restriction cannot depend on which operational proof recovered the cursor. -/
instance {whole : Graph Player L Γ₀ Δ} {suffix : Graph Player L Γ Δ} {length : Nat} :
    Subsingleton (Prefix Δ whole suffix length) where
  allEq left right := by
    induction left with
    | refl => cases right; rfl
    | sample left ih =>
        cases right with
        | sample right => exact congrArg Prefix.sample (ih right)
    | bind left ih =>
        cases right with
        | bind right => exact congrArg Prefix.bind (ih right)
    | resolve left ih =>
        cases right with
        | resolve right => exact congrArg Prefix.resolve (ih right)

private theorem policyTail_mpr_length {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {n m : Nat} (same : n = m)
    (typeEq : Prefix Δ whole suffix n = Prefix Δ whole suffix m)
    (walk : Prefix Δ whole suffix m) (who : Player)
    (policy : BehavioralPolicy who whole) :
    policyTail who (Eq.mpr typeEq walk) policy = policyTail who walk policy := by
  subst m
  rfl

private theorem policyTail_mp_length {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {n m : Nat} (same : n = m)
    (typeEq : Prefix Δ whole suffix n = Prefix Δ whole suffix m)
    (walk : Prefix Δ whole suffix n) (who : Player)
    (policy : BehavioralPolicy who whole) :
    policyTail who (Eq.mp typeEq walk) policy = policyTail who walk policy := by
  subst m
  rfl

/-- Policy restriction composes along consecutive typed graph prefixes. -/
theorem policyTail_trans {whole : Graph Player L Γ₀ Δ}
    {middle : Graph Player L Γ Δ} {target : VCtx Player L}
    {suffix : Graph Player L target Δ} {n m : Nat}
    (left : Prefix Δ whole middle n) (right : Prefix Δ middle suffix m)
    (who : Player) (policy : BehavioralPolicy who whole) :
    (left.trans right).policyTail who policy =
      right.policyTail who (left.policyTail who policy) := by
  induction left with
  | refl =>
      simp only [trans, policyTail]
      rw [policyTail_mpr_length (by omega)]
  | sample left ih =>
      simp only [trans]
      rw [policyTail_mpr_length (by omega), policyTail_mp_length (by omega)]
      exact ih right policy
  | bind left ih =>
      simp only [trans]
      rw [policyTail_mpr_length (by omega), policyTail_mp_length (by omega)]
      exact ih right policy.2
  | resolve left ih =>
      simp only [trans]
      rw [policyTail_mpr_length (by omega), policyTail_mp_length (by omega)]
      exact ih right policy.2

/-- Restricting a whole profile has the same composition law. -/
theorem profileTail_trans {whole : Graph Player L Γ₀ Δ}
    {middle : Graph Player L Γ Δ} {target : VCtx Player L}
    {suffix : Graph Player L target Δ} {n m : Nat}
    (left : Prefix Δ whole middle n) (right : Prefix Δ middle suffix m)
    (profile : BehavioralProfile whole) :
    (left.trans right).profileTail profile =
      right.profileTail (left.profileTail profile) := by
  funext who
  exact left.policyTail_trans right who (profile who)

end Vegas.GraphRuntime.Prefix
