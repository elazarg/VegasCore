/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDecisionCheckpoints

/-! # Source policies extracted from actual windowed prefixes

Actual focal source edges are connected to this policy in
`Vegas.Compile.WindowedSourceDecisionCoverage`. Whole-execution correspondence
additionally requires composing the joint source/native block laws.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext : VCtx P L} {rootPending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}

/-- Glue the actual decision representatives at every suffix of a fixed
windowed application into a source-policy checkpoint family. -/
def sourcePolicyCheckpointsFrom
    (root : ApplicationPlan rootAccounted rootFresh rootState)
    (rootProfile : SourceBehavioralProfile rootProg) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ owner, instruction.submitter = some owner → owner ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal)
    (blockIndex : Nat)
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (plan : ApplicationPlan accounted fresh state) (profile : SourceBehavioralProfile prog) :
    SourcePolicyCheckpoints prog focal := by
  induction plan generalizing blockIndex with
  | ret => exact SourcePolicyCheckpoints.ret
  | sample next ih =>
      exact SourcePolicyCheckpoints.sample (ih profile.afterSample (blockIndex := blockIndex + 1))
  | @binding Γ pending name owner ty guard tail newName accounted fresh state unrestricted
      next ih =>
      by_cases howner : owner = focal
      · subst owner
        let head := bindingDecisionCheckpoints (newName := newName) (fresh := fresh)
          root rootProfile deadlineOf binding choice windowOf
          roster focal replacement initial blockIndex unrestricted next profile hinitial horigins
          hroster howners command hpure relay hrelay hrelayOther
        exact SourcePolicyCheckpoints.ownedCommit head
          (ih profile.afterCommit (blockIndex := blockIndex + 1))
      · exact SourcePolicyCheckpoints.otherCommit howner
          (ih profile.afterCommit (blockIndex := blockIndex + 1))
  | @publicChoice Γ pending name publicName owner ty guard tail newName unresolved accounted fresh
      state publicGuard next ih =>
      by_cases howner : owner = focal
      · subst owner
        let plan := ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
          (fresh := fresh) publicGuard next
        let code := (PublicChoiceSite.atHead name publicName focal guard tail).code fresh state
        let head := publicDecisionCheckpoints root rootProfile deadlineOf binding choice windowOf
          roster focal replacement initial blockIndex plan profile hinitial horigins hroster howners
          command hpure (.publicChoice code) (next.instructions deadlineOf) rfl rfl
        exact SourcePolicyCheckpoints.ownedCommit head
          (SourcePolicyCheckpoints.reveal
            (ih profile.afterCommit.afterReveal (blockIndex := blockIndex + 1)))
      · exact SourcePolicyCheckpoints.otherCommit howner
          (SourcePolicyCheckpoints.reveal
            (ih profile.afterCommit.afterReveal (blockIndex := blockIndex + 1)))
  | @conditional Γ pending name publicName owner ty guard tail spec unresolved newName accounted
      fresh state publicGuard next ih =>
      by_cases howner : owner = focal
      · subst owner
        let plan := ApplicationPlan.conditional (unresolved := unresolved) (newName := newName)
          (fresh := fresh) publicGuard next
        let site := ConditionalPublicationSite.atHead name publicName focal guard tail spec
        let code := site.code fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state))
        let head := publicDecisionCheckpoints root rootProfile deadlineOf binding choice windowOf
          roster focal replacement initial blockIndex plan profile hinitial horigins hroster howners
          command hpure (.conditional code) (next.instructions deadlineOf) rfl rfl
        exact SourcePolicyCheckpoints.ownedCommit head
          (SourcePolicyCheckpoints.reveal
            (ih profile.afterCommit.afterReveal (blockIndex := blockIndex + 1)))
      · exact SourcePolicyCheckpoints.otherCommit howner
          (SourcePolicyCheckpoints.reveal
            (ih profile.afterCommit.afterReveal (blockIndex := blockIndex + 1)))
  | @conditionalCopy Γ pending name publicName owner ty guard tail spec newName unresolved accounted
      fresh state publicGuard next ih =>
      by_cases howner : owner = focal
      · subst owner
        let plan := ApplicationPlan.conditionalCopy (newName := newName)
          (unresolved := unresolved) (fresh := fresh) spec publicGuard next
        let site := ConditionalPublicationSite.atHead name publicName focal guard tail spec
        let code := site.code fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state))
        let head := publicDecisionCheckpoints root rootProfile deadlineOf binding choice windowOf
          roster focal replacement initial blockIndex plan profile hinitial horigins hroster howners
          command hpure (.conditional code) (next.instructions deadlineOf) rfl rfl
        exact SourcePolicyCheckpoints.ownedCommit head
          (SourcePolicyCheckpoints.reveal
            (ih profile.afterCommit.afterReveal (blockIndex := blockIndex + 1)))
      · exact SourcePolicyCheckpoints.otherCommit howner
          (SourcePolicyCheckpoints.reveal
            (ih profile.afterCommit.afterReveal (blockIndex := blockIndex + 1)))

/-- The checkpoint family rooted at the initial structural position. -/
def sourcePolicyCheckpoints
    (root : ApplicationPlan rootAccounted rootFresh rootState)
    (rootProfile : SourceBehavioralProfile rootProg) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ owner, instruction.submitter = some owner → owner ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    SourcePolicyCheckpoints rootProg focal :=
  sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice windowOf roster focal
    replacement initial hinitial horigins hroster howners command hpure relay hrelay hrelayOther
    0 root rootProfile

/-- Total source policy obtained by using extracted checkpoint actions where
available and the original source profile elsewhere. -/
def extractedSourcePolicy
    (root : ApplicationPlan rootAccounted rootFresh rootState)
    (rootProfile : SourceBehavioralProfile rootProg) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ owner, instruction.submitter = some owner → owner ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    SourceBehavioralPolicy rootProg focal :=
  SourcePolicyCheckpoints.extend
    (sourcePolicyCheckpoints root rootProfile deadlineOf binding choice windowOf roster focal
    replacement initial hinitial horigins hroster howners command hpure relay hrelay
    hrelayOther) (rootProfile focal)

/-- At every actual representative in the recursively glued family, the
extracted source policy is exactly the pure recorded legal action. -/
theorem extractedSourcePolicy_at_checkpoint
    (root : ApplicationPlan rootAccounted rootFresh rootState)
    (rootProfile : SourceBehavioralProfile rootProg) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ owner, instruction.submitter = some owner → owner ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    let checkpoints : SourcePolicyCheckpoints rootProg focal :=
      sourcePolicyCheckpoints root rootProfile deadlineOf binding choice windowOf
      roster focal replacement initial hinitial horigins hroster howners command hpure relay
      hrelay hrelayOther
    ∀ {Δ x b guard} (site : SourceDecisionSite focal rootProg Δ x b guard)
      (checkpoint : (checkpoints site).Carrier),
      extractedSourcePolicy root rootProfile deadlineOf binding choice windowOf roster focal
          replacement initial hinitial horigins hroster howners command hpure relay hrelay
          hrelayOther site ((checkpoints site).visible checkpoint) =
        FinDist.pure ((checkpoints site).action checkpoint) := by
  dsimp only
  intro Δ x b guard site checkpoint
  unfold extractedSourcePolicy
  exact SourcePolicyCheckpoints.extend_at_checkpoint _ _ site checkpoint

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.extractedSourcePolicy_at_checkpoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.extractedSourcePolicy_at_checkpoint
