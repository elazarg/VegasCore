/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationProfileContinuation
import Vegas.Compile.PublicResolution

/-! # Source-certified fallbacks for complete block service

This static predicate checks the emitted timeout selectors against source
fallback expressions. It is a backend eligibility condition, not a restriction
on runtime commands or a change to source well-formedness. Chance needs no
fallback, and conditional publication already has its source-certified `none`
outcome.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Each unconditional player instruction is equipped with the programmer's
source-certified public fallback, at the code actually emitted for that site. -/
def BlockFallbacks
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state) : Prop := by
  induction plan with
  | ret => exact True
  | sample next ih => exact ih
  | @binding Γ pending name owner ty guard tail newName accounted fresh state
      unrestricted next ih =>
      let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
        .here guard tail
      exact (∃ (fallback : SourceDecisionSite.PublicFallback site) (deadline : Nat),
        binding (site.bindingCode fresh state (site.compiledField fresh state)) =
          some ⟨deadline, fallback.compiled fresh state⟩) ∧ ih
  | @publicChoice Γ pending name publicName owner ty guard tail newName unresolved
      accounted fresh state publicGuard next ih =>
      let site := PublicChoiceSite.atHead name publicName owner guard tail
      exact (∃ (fallback : SourceDecisionSite.PublicFallback site.decision) (deadline : Nat),
        choice (site.code fresh state) = some ⟨deadline, fallback.compiled fresh state⟩) ∧ ih
  | conditional publicGuard next ih => exact ih
  | conditionalCopy spec publicGuard next ih => exact ih

namespace ProfileContinuation

/-- Traversing the original compiled source retains the timeout certificates
for its remaining instructions. -/
theorem blockFallbacks
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {plan : ApplicationPlan accounted fresh state}
    {rootProfile : SourceBehavioralProfile rootProg} {profile : SourceBehavioralProfile prog}
    (continuation : ProfileContinuation root rootProfile plan profile)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (hfallbacks : root.BlockFallbacks binding choice) : plan.BlockFallbacks binding choice := by
  induction continuation with
  | refl => exact hfallbacks
  | sample previous ih => exact ih
  | binding previous ih => exact ih.2
  | publicChoice previous ih => exact ih.2
  | conditional previous ih => exact ih
  | conditionalCopy previous ih => exact ih

end ProfileContinuation

end Vegas.ApplicationPlan
