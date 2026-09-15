/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.Settlement

/-! # Prefix-relative source quitting comparisons

This module compares two terminal written-source executions at a particular
source decision.  The quitting execution is legal and records the designated
typed value.  The continuing execution is supported by a unilateral source
alternative against fixed opponents.  Their public source environments must
agree strictly before the decision.

The condition contains no runtime state or correspondence premise.  A compiler
theorem must separately prove that the terminal pair produced for a timeout
has the required source-prefix equality.
-/

noncomputable section

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace SourceDecisionSite

/-- At one typed decision site, quitting is no better than every supported
unilateral continuation having the same public source prefix strictly before
that decision. -/
def QuitPrefixDominatesAgainst
    {Γ Δ : VCtx P L} {prog : VegasCore P L Γ} {who : P}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (initial : VEnv L Γ) (quit : L.Val ty)
    (utility : VEnv L (sourceTerminalCtx prog) → P → ℝ)
    (profile : SourceBehavioralProfile prog) : Prop :=
  ∀ (alternative : SourceBehavioralPolicy prog who)
    (quitting continued : VEnv L (sourceTerminalCtx prog)),
    SmallStep.Star ⟨Γ, initial, prog⟩
      ⟨sourceTerminalCtx prog, quitting, .ret (sourceTerminalPayoffs prog)⟩ →
    (site.recorded quitting).get .here = quit →
    continued ∈ (denoteSource prog
      (Profile.update (sig := sourceGameSignature prog) profile who alternative)
      initial).support →
    (site.recorded quitting).tail.erasePubEnv =
      (site.recorded continued).tail.erasePubEnv →
    utility quitting who ≤ utility continued who

end SourceDecisionSite

namespace VegasCore

/-- Prefix-relative quitting dominance at every decision of the designated
value type. -/
def QuitPrefixDominanceAgainst {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (initial : VEnv L Γ) {ty : L.Ty} (quit : L.Val ty)
    (utility : VEnv L (sourceTerminalCtx prog) → P → ℝ)
    (profile : SourceBehavioralProfile prog) : Prop :=
  ∀ (who : P) (Δ : VCtx P L) (name : VarId)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool)
    (site : SourceDecisionSite who prog Δ name ty guard),
    site.QuitPrefixDominatesAgainst initial quit utility profile

/-- Prefix-relative dominance specialized to the written terminal payout. -/
def QuitPayoutPrefixDominanceAgainst {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (initial : VEnv L Γ) {ty : L.Ty} (quit : L.Val ty)
    (valuation : Payout P → P → ℝ) (profile : SourceBehavioralProfile prog) : Prop :=
  prog.QuitPrefixDominanceAgainst initial quit
    (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs prog) final) who)
    profile

/-- Coincident global quitting cap and fixed-opponent support floor imply the
prefix-relative comparison.  This implication intentionally does not use the
prefix equality. -/
theorem QuitPayoutBoundAgainst.quitPayoutPrefixDominance
    {Γ : VCtx P L} {prog : VegasCore P L Γ} {initial : VEnv L Γ}
    {ty : L.Ty} {quit : L.Val ty} {valuation : Payout P → P → ℝ}
    {bound : P → ℝ} {profile : SourceBehavioralProfile prog}
    (hbound : prog.QuitPayoutBoundAgainst initial quit valuation bound profile) :
    prog.QuitPayoutPrefixDominanceAgainst initial quit valuation profile := by
  intro who Δ name guard site alternative quitting continued hquitting hquit hcontinued _
  have hupper := hbound.quit_upper quitting hquitting who
    ⟨Δ, name, guard, site, hquit⟩
  have hlower := hbound.lower who alternative continued hcontinued
  exact hupper.trans hlower

end VegasCore

end Vegas

/-- info: 'Vegas.VegasCore.QuitPayoutBoundAgainst.quitPayoutPrefixDominance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.VegasCore.QuitPayoutBoundAgainst.quitPayoutPrefixDominance
