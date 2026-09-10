/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationDeadlines
import Vegas.Compile.ApplicationBindingTimeouts

/-! # Deadline replacement for generated application plans

Retiming a canonical generated image is exactly regeneration with the new
deadline function. Generated binding and ordinary public-choice instructions
have no fallback metadata; conditional instructions carry the supplied
deadline directly.

For an image subsequently decorated with optional fallbacks, the transformed
selectors below first restore the canonical undecorated code before applying
the original selector, then retime its result. This permits arbitrary selectors
that inspect their code argument without falsely asserting selector invariance.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Instruction-list form of canonical plan retiming. -/
theorem instructions_withDeadlines
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (first second : Nat → Nat) :
    (plan.instructions first).map
        (ApplicationInstruction.withDeadlines second) =
      plan.instructions second := by
  induction plan with
  | ret => rfl
  | sample next ih =>
      simp only [instructions, List.map_cons, ApplicationInstruction.withDeadlines]
      rw [ih]
  | binding unrestricted next ih =>
      simp only [instructions, List.map_cons, ApplicationInstruction.withDeadlines,
        SourceDecisionSite.bindingCode, Option.map_none]
      rw [ih]
  | publicChoice publicGuard next ih =>
      simp only [instructions, List.map_cons, ApplicationInstruction.withDeadlines,
        PublicChoiceSite.code, Option.map_none]
      rw [ih]
  | conditional publicGuard next ih | conditionalCopy spec publicGuard next ih =>
      simp only [instructions, List.map_cons, ApplicationInstruction.withDeadlines]
      rw [ih]
      rfl

/-- Retiming the canonical emitted image gives the same artifact as
regenerating the plan with the replacement deadline function. -/
theorem image_withDeadlines
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (first second : Nat → Nat) :
    (plan.image first).withDeadlines second = plan.image second := by
  change ApplicationImage.mk ((plan.instructions first).map
      (ApplicationInstruction.withDeadlines second)) =
    ApplicationImage.mk (plan.instructions second)
  rw [plan.instructions_withDeadlines first second]

/-- Reapply a binding selector to canonical code and replace the deadline of
any fallback it installs. -/
def retimedBindingSelector (deadlineOf : Nat → Nat)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (code : BindingCode P L) : Option (PublicFallbackCode L code.ty) :=
  (select { code with timeout := none }).map fun timeout =>
    { timeout with deadline := deadlineOf code.node }

/-- Reapply a public-choice selector to canonical code and replace the deadline
of any fallback it installs. -/
def retimedChoiceSelector (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (code : PublicChoiceCode P L) : Option (PublicFallbackCode L code.guard.ty) :=
  (select { code with timeout := none }).map fun timeout =>
    { timeout with deadline := deadlineOf code.endpoint.publicationNode }

/-- Retiming a fully decorated generated plan equals decorating the canonically
retimed plan with selectors whose results carry the replacement deadlines.
Selectors may inspect every field of their original canonical code argument. -/
theorem instructions_timeouts_withDeadlines
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (first second : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty)) :
    (((plan.instructions first).map
        (ApplicationInstruction.withBindingTimeouts binding)).map
      (ApplicationInstruction.withChoiceTimeouts choice)).map
        (ApplicationInstruction.withDeadlines second) =
      ((plan.instructions second).map
        (ApplicationInstruction.withBindingTimeouts
          (retimedBindingSelector second binding))).map
        (ApplicationInstruction.withChoiceTimeouts
          (retimedChoiceSelector second choice)) := by
  induction plan with
  | ret => rfl
  | sample next ih =>
      simp only [instructions, List.map_cons, ApplicationInstruction.withBindingTimeouts,
        ApplicationInstruction.withChoiceTimeouts, ApplicationInstruction.withDeadlines]
      rw [ih]
  | binding unrestricted next ih =>
      simp only [instructions, List.map_cons, ApplicationInstruction.withBindingTimeouts,
        ApplicationInstruction.withChoiceTimeouts, ApplicationInstruction.withDeadlines,
        SourceDecisionSite.bindingCode, retimedBindingSelector]
      rw [ih]
  | publicChoice publicGuard next ih =>
      simp only [instructions, List.map_cons, ApplicationInstruction.withBindingTimeouts,
        ApplicationInstruction.withChoiceTimeouts, ApplicationInstruction.withDeadlines,
        PublicChoiceSite.code, retimedChoiceSelector]
      rw [ih]
  | conditional publicGuard next ih | conditionalCopy spec publicGuard next ih =>
      simp only [instructions, List.map_cons, ApplicationInstruction.withBindingTimeouts,
        ApplicationInstruction.withChoiceTimeouts, ApplicationInstruction.withDeadlines]
      rw [ih]
      rfl

/-- Image form of `instructions_timeouts_withDeadlines`. -/
theorem image_timeouts_withDeadlines
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (first second : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty)) :
    ApplicationImage.withDeadlines
        (((plan.image first).withBindingTimeouts binding).withChoiceTimeouts choice)
        second =
      ((plan.image second).withBindingTimeouts
        (retimedBindingSelector second binding)).withChoiceTimeouts
          (retimedChoiceSelector second choice) := by
  change ApplicationImage.mk
      ((((plan.instructions first).map
            (ApplicationInstruction.withBindingTimeouts binding)).map
          (ApplicationInstruction.withChoiceTimeouts choice)).map
        (ApplicationInstruction.withDeadlines second)) =
    ApplicationImage.mk
      (((plan.instructions second).map
          (ApplicationInstruction.withBindingTimeouts
            (retimedBindingSelector second binding))).map
        (ApplicationInstruction.withChoiceTimeouts
          (retimedChoiceSelector second choice)))
  rw [plan.instructions_timeouts_withDeadlines first second binding choice]

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.image_withDeadlines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.image_withDeadlines

/-- info: 'Vegas.ApplicationPlan.image_timeouts_withDeadlines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.image_timeouts_withDeadlines
