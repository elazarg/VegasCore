/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPolicyContinuation

/-! # Coverage of focal source decisions by the extracted policy

An actual focal-owned block selects a decision of the original source program.
The extracted policy chooses its recorded value, and the remaining source
steps reach the recorded successor. This is a local action statement; it
does not assert equality of complete execution distributions.
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
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal relay : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
variable (hinitial : root.InitialControllerReadsPublic)
variable (horigins : (root.image deadlineOf).HasBindingOrigins) (hroster : roster.Nodup)
variable (howners : ∀ instruction ∈ root.instructions deadlineOf,
  ∀ owner, instruction.submitter = some owner → owner ∈ roster)
variable (command :
  List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
    (root.windowed deadlineOf binding choice windowOf).application.View →
      (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
variable (hpure : replacement = fun history view => FinDist.pure (command history view))
variable (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal)

private theorem root_kernel_of_suffix
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} {blockIndex : Nat}
    {plan : ApplicationPlan accounted fresh state} {profile : SourceBehavioralProfile prog}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
      replacement initial blockIndex plan profile current execution)
    {Δ : VCtx P L} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx focal Δ)) L.bool}
    (site : SourceDecisionSite focal prog Δ name ty guard)
    (visible : Env L.Val (eraseVCtx (viewVCtx focal Δ)))
    (law : FinDist {value : L.Val ty // evalGuard guard value visible = true})
    (hlocal : (sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice windowOf
      roster focal replacement initial hinitial horigins hroster howners command hpure relay
      hrelay hrelayOther blockIndex plan profile site).extend (profile focal site) visible = law) :
    ∃ rootSite : SourceDecisionSite focal rootProg Δ name ty guard,
      extractedSourcePolicy root rootProfile deadlineOf binding choice windowOf roster focal
        replacement initial hinitial horigins hroster howners command hpure relay hrelay
        hrelayOther rootSite visible = law := by
  obtain ⟨rootSite, hfamily, hprofile⟩ :=
    trace.exists_root_sourceDecisionSite hinitial horigins hroster howners command hpure
      hrelay hrelayOther site
  refine ⟨rootSite, ?_⟩
  change (sourcePolicyCheckpoints root rootProfile deadlineOf binding choice windowOf roster focal
    replacement initial hinitial horigins hroster howners command hpure relay hrelay
    hrelayOther rootSite).extend (rootProfile focal rootSite) visible = law
  rw [hfamily, hprofile]
  exact hlocal

/-- Every actual focal-owned block supplies the canonical head decision of the
suffix checkpoint family. Its chosen value leads by the remaining source steps
to the actual recorded successor. No action agreement is assumed here. -/
theorem BlockSourceStep.exists_focal_local_source_choice
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
    {nextPlan : ApplicationPlan nextAccounted nextFresh nextState}
    {profile : SourceBehavioralProfile prog} {nextProfile : SourceBehavioralProfile nextProg}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {sourceNext : CoupledAt (compileCore nextProg nextFresh nextState).graph nextState}
    {execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
      replacement initial blockIndex plan profile current execution)
    (block : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support)
    (source : BlockSourceStep binding final.native.application.base plan profile current
      nextPlan nextProfile sourceNext)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement (blockIndex + 1) nextPlan nextProfile sourceNext final)
    (howner : (plan.instructions deadlineOf).head?.bind ApplicationInstruction.submitter =
      some focal) :
    ∃ (name : VarId) (ty : L.Ty)
      (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx focal Γ)) L.bool)
      (tail : VegasCore P L ((name, .sealed focal ty) :: Γ))
      (hprog : prog = .commit name focal guard tail) (value : L.Val ty)
      (legal : evalGuard guard value ((current.current.source.toView focal).eraseEnv) = true),
      let site : SourceDecisionSite focal prog Γ name ty guard :=
        hprog.symm ▸ SourceDecisionSite.here guard tail
      (sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice windowOf roster focal
        replacement initial hinitial horigins hroster howners command hpure relay hrelay
        hrelayOther blockIndex plan profile site).extend (profile focal site)
          ((current.current.source.toView focal).eraseEnv) =
          FinDist.pure ⟨value, legal⟩ ∧
      SmallStep.Star ⟨(name, .sealed focal ty) :: Γ, current.current.source.cons value, tail⟩
        ⟨Δ, sourceNext.current.source, nextProg⟩ := by
  cases source with
  | sample value draw hsource =>
      simp [instructions, ApplicationInstruction.submitter] at howner
  | @binding pending name owner ty guard tail newName accounted fresh state unrestricted
      next profile current sourceNext fallback deadline selected value hsource resolved =>
      have heq : owner = focal := by
        exact Option.some.inj howner
      subst owner
      let plan := ApplicationPlan.binding (newName := newName) (fresh := fresh)
        unrestricted next
      let head := bindingDecisionCheckpoints (newName := newName) (fresh := fresh)
        root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
        blockIndex unrestricted next profile hinitial horigins hroster howners command hpure
        relay hrelay hrelayOther
      let witness : head.Carrier :=
        ⟨current, execution, final, trace, fallback, deadline, selected, block⟩
      have hlocal := head.extend_at_checkpoint (profile focal (.here guard tail)) witness
      have haction : (head.action witness).1 = value := resolved.symm
      have hlocal' : head.extend (profile focal (.here guard tail))
          ((current.current.source.toView focal).eraseEnv) =
          FinDist.pure ⟨value, unrestricted current.current.source value⟩ := by
        exact hlocal.trans (congrArg FinDist.pure (Subtype.ext haction))
      have hlocalHead := (show
        (sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice windowOf roster
          focal replacement initial hinitial horigins hroster howners command hpure relay hrelay
          hrelayOther blockIndex plan profile (.here guard tail)).extend
            (profile focal (.here guard tail)) _ = _ by
        simpa [sourcePolicyCheckpointsFrom, plan,
          SourcePolicyCheckpoints.ownedCommit, head] using hlocal')
      refine ⟨name, ty, guard, tail, rfl, value, unrestricted _ _, hlocalHead, ?_⟩
      rw [hsource]
      exact .refl _
  | @publicChoice pending name publicName owner ty guard tail newName unresolved accounted
      fresh state publicGuard next profile current sourceNext value hsource legal =>
      have heq : owner = focal := by
        exact Option.some.inj howner
      subst owner
      let plan := ApplicationPlan.publicChoice (newName := newName)
        (unresolved := unresolved) (fresh := fresh) publicGuard next
      let code := (PublicChoiceSite.atHead name publicName focal guard tail).code fresh state
      let head := publicDecisionCheckpoints root rootProfile deadlineOf binding choice windowOf
        roster focal replacement initial blockIndex plan profile hinitial horigins hroster howners
        command hpure (.publicChoice code) (next.instructions deadlineOf) rfl rfl
      let witness : head.Carrier :=
        ⟨current, execution, final, trace, value, legal, sourceNext, hsource,
          checkpoint.refines, block⟩
      have hlocal := head.extend_at_checkpoint (profile focal (.here guard _)) witness
      have hlocalHead := (show
        (sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice windowOf roster
          focal replacement initial hinitial horigins hroster howners command hpure relay hrelay
          hrelayOther blockIndex plan profile (.here guard _)).extend
            (profile focal (.here guard _)) _ = _ by
        simpa [sourcePolicyCheckpointsFrom, plan, SourcePolicyCheckpoints.ownedCommit,
          head, witness, publicDecisionCheckpoints] using hlocal)
      refine ⟨name, ty, guard, _, rfl, value, legal, hlocalHead, ?_⟩
      rw [hsource]
      exact .single (.reveal .here _)
  | @conditional pending name publicName owner ty guard tail spec unresolved newName accounted
      fresh state publicGuard next profile current sourceNext result admissible hsource legal =>
      have heq : owner = focal := by
        exact Option.some.inj howner
      subst owner
      let plan := ApplicationPlan.conditional (newName := newName)
        (unresolved := unresolved) (fresh := fresh) publicGuard next
      let localSite := ConditionalPublicationSite.atHead name publicName focal guard tail spec
      let code := localSite.code fresh state (localSite.sourceField fresh state)
        (deadlineOf (localSite.choice.publicationNode fresh state))
      let head := publicDecisionCheckpoints root rootProfile deadlineOf binding choice windowOf
        roster focal replacement initial blockIndex plan profile hinitial horigins hroster howners
        command hpure (.conditional code) (next.instructions deadlineOf) rfl rfl
      let witness : head.Carrier :=
        ⟨current, execution, final, trace, spec.encoding.symm result, legal, sourceNext, hsource,
          checkpoint.refines, block⟩
      have hlocal := head.extend_at_checkpoint (profile focal (.here guard _)) witness
      have hlocalHead := (show
        (sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice windowOf roster
          focal replacement initial hinitial horigins hroster howners command hpure relay hrelay
          hrelayOther blockIndex plan profile (.here guard _)).extend
            (profile focal (.here guard _)) _ = _ by
        simpa [sourcePolicyCheckpointsFrom, plan, SourcePolicyCheckpoints.ownedCommit,
          head, witness, publicDecisionCheckpoints] using hlocal)
      refine ⟨name, ty, guard, _, rfl, spec.encoding.symm result, legal, hlocalHead, ?_⟩
      rw [hsource]
      exact .single (.reveal .here _)
  | @conditionalCopy pending name publicName owner ty guard tail spec newName unresolved accounted
      fresh state publicGuard next profile current sourceNext result admissible hsource legal =>
      have heq : owner = focal := by
        exact Option.some.inj howner
      subst owner
      let plan := ApplicationPlan.conditionalCopy (newName := newName)
        (unresolved := unresolved) (fresh := fresh) spec publicGuard next
      let localSite := ConditionalPublicationSite.atHead name publicName focal guard tail spec
      let code := localSite.code fresh state (localSite.sourceField fresh state)
        (deadlineOf (localSite.choice.publicationNode fresh state))
      let head := publicDecisionCheckpoints root rootProfile deadlineOf binding choice windowOf
        roster focal replacement initial blockIndex plan profile hinitial horigins hroster howners
        command hpure (.conditional code) (next.instructions deadlineOf) rfl rfl
      let witness : head.Carrier :=
        ⟨current, execution, final, trace, spec.encoding.symm result, legal, sourceNext, hsource,
          checkpoint.refines, block⟩
      have hlocal := head.extend_at_checkpoint (profile focal (.here guard _)) witness
      have hlocalHead := (show
        (sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice windowOf roster
          focal replacement initial hinitial horigins hroster howners command hpure relay hrelay
          hrelayOther blockIndex plan profile (.here guard _)).extend
            (profile focal (.here guard _)) _ = _ by
        simpa [sourcePolicyCheckpointsFrom, plan, SourcePolicyCheckpoints.ownedCommit,
          head, witness, publicDecisionCheckpoints] using hlocal)
      refine ⟨name, ty, guard, _, rfl, spec.encoding.symm result, legal, hlocalHead, ?_⟩
      rw [hsource]
      exact .single (.reveal .here _)

/-- Every actual focal-owned block is implemented by a decision of the single
extracted root policy. The root occurrence is obtained from the suffix-local
checkpoint law, without repeating the block analysis. -/
theorem BlockSourceStep.exists_focal_source_choice
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
    {nextPlan : ApplicationPlan nextAccounted nextFresh nextState}
    {profile : SourceBehavioralProfile prog} {nextProfile : SourceBehavioralProfile nextProg}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {sourceNext : CoupledAt (compileCore nextProg nextFresh nextState).graph nextState}
    {execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
      replacement initial blockIndex plan profile current execution)
    (block : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support)
    (source : BlockSourceStep binding final.native.application.base plan profile current
      nextPlan nextProfile sourceNext)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement (blockIndex + 1) nextPlan nextProfile sourceNext final)
    (howner : (plan.instructions deadlineOf).head?.bind ApplicationInstruction.submitter =
      some focal) :
    ∃ (name : VarId) (ty : L.Ty)
      (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx focal Γ)) L.bool)
      (tail : VegasCore P L ((name, .sealed focal ty) :: Γ))
      (site : SourceDecisionSite focal rootProg Γ name ty guard) (value : L.Val ty)
      (legal : evalGuard guard value ((current.current.source.toView focal).eraseEnv) = true),
      prog = .commit name focal guard tail ∧
      extractedSourcePolicy root rootProfile deadlineOf binding choice windowOf roster focal
        replacement initial hinitial horigins hroster howners command hpure relay hrelay
        hrelayOther site ((current.current.source.toView focal).eraseEnv) =
          FinDist.pure ⟨value, legal⟩ ∧
      SmallStep.Star ⟨(name, .sealed focal ty) :: Γ, current.current.source.cons value, tail⟩
        ⟨Δ, sourceNext.current.source, nextProg⟩ := by
  obtain ⟨name, ty, guard, tail, hprog, value, legal, hlocal, hsteps⟩ :=
    source.exists_focal_local_source_choice hinitial horigins hroster howners command hpure
      hrelay hrelayOther trace block checkpoint howner
  let localSite : SourceDecisionSite focal prog Γ name ty guard :=
    hprog.symm ▸ SourceDecisionSite.here guard tail
  obtain ⟨rootSite, hroot⟩ := root_kernel_of_suffix hinitial horigins hroster howners command
    hpure hrelay hrelayOther trace localSite _ _ hlocal
  exact ⟨name, ty, guard, tail, rootSite, value, legal, hprog, hroot, hsteps⟩

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.BlockSourceStep.exists_focal_local_source_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.BlockSourceStep.exists_focal_local_source_choice

/-- info: 'Vegas.ApplicationPlan.BlockSourceStep.exists_focal_source_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.BlockSourceStep.exists_focal_source_choice
