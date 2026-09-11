/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourcePolicy

/-! # Lifting suffix decision checkpoints to the root source policy -/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedSourcePrefix

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext : VCtx P L} {rootPending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal relay : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}

/-- Every suffix decision family reached by an actual source prefix is the
corresponding occurrence in the checkpoint family of the original program. -/
theorem exists_root_sourceDecisionSite
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ owner, instruction.submitter = some owner → owner ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal)
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} {blockIndex : Nat}
    {plan : ApplicationPlan accounted fresh state} {profile : SourceBehavioralProfile prog}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
      replacement initial blockIndex plan profile current execution)
    {Δ : VCtx P L} {x : VarId} {ty : L.Ty}
    {guard : L.Expr ((x, ty) :: eraseVCtx (viewVCtx focal Δ)) L.bool}
    (site : SourceDecisionSite focal prog Δ x ty guard) :
    ∃ rootSite : SourceDecisionSite focal rootProg Δ x ty guard,
      sourcePolicyCheckpoints root rootProfile deadlineOf binding choice windowOf roster focal
          replacement initial hinitial horigins hroster howners command hpure relay hrelay
          hrelayOther rootSite =
        sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice windowOf roster focal
          replacement initial hinitial horigins hroster howners command hpure relay hrelay
          hrelayOther blockIndex plan profile site ∧
      rootProfile focal rootSite = profile focal site := by
  induction trace with
  | initial checkpoint =>
      exact ⟨site, rfl, rfl⟩
  | @step Γ nextΓ pending nextPending prog nextProg accounted nextAccounted fresh nextFresh state
      nextState blockIndex plan nextPlan profile nextProfile current sourceNext execution final
      previous block source checkpoint ih =>
      cases source with
      | @sample pending name ty dist tail accounted fresh state next profile current sourceNext
          value draw hsource =>
          obtain ⟨rootSite, hfamily, hprofile⟩ := ih (.sample site)
          refine ⟨rootSite, ?_, ?_⟩
          · simpa [sourcePolicyCheckpointsFrom, SourcePolicyCheckpoints.sample] using hfamily
          · simpa [SourceBehavioralProfile.afterSample] using hprofile
      | @binding pending name owner ty guard tail newName accounted fresh state unrestricted next
          profile current sourceNext fallback deadline selected value hsource resolved =>
          obtain ⟨rootSite, hfamily, hprofile⟩ := ih (.commit site)
          refine ⟨rootSite, ?_, ?_⟩
          · by_cases howner : owner = focal
            · subst owner
              simpa [sourcePolicyCheckpointsFrom, SourcePolicyCheckpoints.ownedCommit] using hfamily
            · simpa [sourcePolicyCheckpointsFrom, howner,
                SourcePolicyCheckpoints.otherCommit] using hfamily
          · simpa [SourceBehavioralProfile.afterCommit] using hprofile
      | @publicChoice pending name publicName owner ty guard tail newName unresolved accounted
          fresh state publicGuard next profile current sourceNext value hsource legal =>
          obtain ⟨rootSite, hfamily, hprofile⟩ := ih (.commit (.reveal site))
          refine ⟨rootSite, ?_, ?_⟩
          · by_cases howner : owner = focal
            · subst owner
              simpa [sourcePolicyCheckpointsFrom, SourcePolicyCheckpoints.ownedCommit,
                SourcePolicyCheckpoints.reveal] using hfamily
            · simpa [sourcePolicyCheckpointsFrom, howner, SourcePolicyCheckpoints.otherCommit,
                SourcePolicyCheckpoints.reveal] using hfamily
          · simpa [SourceBehavioralProfile.afterCommit,
              SourceBehavioralProfile.afterReveal] using hprofile
      | @conditional pending name publicName owner ty guard tail spec unresolved newName
          accounted fresh state publicGuard next profile current sourceNext result admissible
          hsource legal =>
          obtain ⟨rootSite, hfamily, hprofile⟩ := ih (.commit (.reveal site))
          refine ⟨rootSite, ?_, ?_⟩
          · by_cases howner : owner = focal
            · subst owner
              simpa [sourcePolicyCheckpointsFrom, SourcePolicyCheckpoints.ownedCommit,
                SourcePolicyCheckpoints.reveal] using hfamily
            · simpa [sourcePolicyCheckpointsFrom, howner, SourcePolicyCheckpoints.otherCommit,
                SourcePolicyCheckpoints.reveal] using hfamily
          · simpa [SourceBehavioralProfile.afterCommit,
              SourceBehavioralProfile.afterReveal] using hprofile
      | @conditionalCopy pending name publicName owner ty guard tail specification newName
          unresolved accounted fresh state publicGuard next profile current sourceNext result
          admissible hsource legal =>
          obtain ⟨rootSite, hfamily, hprofile⟩ := ih (.commit (.reveal site))
          refine ⟨rootSite, ?_, ?_⟩
          · by_cases howner : owner = focal
            · subst owner
              simpa [sourcePolicyCheckpointsFrom, SourcePolicyCheckpoints.ownedCommit,
                SourcePolicyCheckpoints.reveal] using hfamily
            · simpa [sourcePolicyCheckpointsFrom, howner, SourcePolicyCheckpoints.otherCommit,
                SourcePolicyCheckpoints.reveal] using hfamily
          · simpa [SourceBehavioralProfile.afterCommit,
              SourceBehavioralProfile.afterReveal] using hprofile

end Vegas.ApplicationPlan.WindowedSourcePrefix

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.exists_root_sourceDecisionSite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedSourcePrefix.exists_root_sourceDecisionSite
