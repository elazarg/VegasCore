/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicy
import Vegas.Compile.ApplicationInitialReads

/-! # The two source-accounting cases of a conditional instruction

This proof-only classification identifies existing application-plan heads that
emit the same conditional runtime instruction and reference policy. Discharging
an original binding and publishing a retained copy differ in source accounting;
neither requires a different operational comparison. No syntax is added.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Evidence that a plan head is either a conditional discharge or a copy,
with the specified source opening certificate. -/
inductive ConditionalHead
    {Γ : VCtx P L} {name publicName : VarId} {owner : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
    (spec : ConditionalOpening guard)
    {fresh : FreshBindings (.commit name owner guard (.reveal publicName owner name .here tail))}
    {state : BuildState P L Γ} :
    {pending : Finset VarId} →
    {accounted : CommitmentAccounting pending
      (.commit name owner guard (.reveal publicName owner name .here tail))} →
    ApplicationPlan accounted fresh state → Prop where
  | discharge {pending : Finset VarId} {unresolved : spec.source ∈ pending}
      {newName : name ∉ pending}
      {accounted : CommitmentAccounting (pending.erase spec.source) tail}
      (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.PubliclyValidatable fresh state)
      (next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1) :
      ConditionalHead spec (.conditional (unresolved := unresolved) (newName := newName)
        publicGuard next)
  | copy {pending : Finset VarId} {newName : name ∉ pending}
      {unresolved : name ∈ insert name pending}
      {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
      (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.PubliclyValidatable fresh state)
      (next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1) :
      ConditionalHead spec (.conditionalCopy (newName := newName) (unresolved := unresolved)
        spec publicGuard next)

namespace ConditionalHead

variable {Γ : VCtx P L} {name publicName : VarId} {owner : P} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ} {pending : Finset VarId}
variable {accounted : CommitmentAccounting pending
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {plan : ApplicationPlan accounted fresh state}

theorem instructions (head : ConditionalHead spec plan) (deadlineOf : Nat → Nat) :
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    ∃ rest, plan.instructions deadlineOf =
      .conditional (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))) :: rest := by
  cases head <;> exact ⟨_, rfl⟩

theorem publiclyValidatable (head : ConditionalHead spec plan) :
    (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state := by
  cases head with
  | discharge publicGuard _ => exact publicGuard
  | copy publicGuard _ => exact publicGuard

theorem initialReadsPublic (head : ConditionalHead spec plan)
    (hinitial : plan.InitialControllerReadsPublic) :
    BuildResult.InitialReadsPublic
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state) (eventGuardOf state owner guard).choiceReads := by
  cases head <;> exact hinitial.1

/-- Both accounting cases select the same reference policy while this
publication remains unresolved. -/
theorem liftProfileIn (head : ConditionalHead spec plan)
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (hunresolved : view.application.done (state.nodes.length + 1) = false) :
    plan.liftProfileIn image deadlineOf profile owner history view =
      let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      site.imagePolicy fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state)) image
        (image.ownerReadout? owner (site.choice.compiledGuard fresh state).choiceReads)
        (profile owner site.choice.decision) (fun _ _ => false) history view := by
  cases head <;>
    simp only [ApplicationPlan.liftProfileIn, hunresolved, Bool.false_eq_true, ↓reduceIte]

end ConditionalHead
end Vegas.ApplicationPlan
