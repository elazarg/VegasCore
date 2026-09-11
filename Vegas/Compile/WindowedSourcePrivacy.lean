/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPrefixShape
import Vegas.Compile.WindowedOwnedCheckpoint
import Vegas.Compile.WindowedBindingPrivacy
import Vegas.Compile.WindowedSamplePrivacy
import Vegas.Compile.WindowedPublicChoicePrivacy
import Vegas.Compile.WindowedConditionalBlockPrivacy

/-! # Source-indexed information preservation through native execution prefixes -/

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
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}

/-- Each actual source extension preserves focal runtime information when
the predecessor executions agree and the successor source views agree.
Every instruction owner is polled; the focal replacement retains all raw
commands. The result compares supported complete native blocks, rather than
assuming a match between their internal submission branches. -/
theorem BlockSourceStep.policyAgreement
    {before after : ProfilePoint P L} {blockIndex : Nat}
    {left right finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (leftEdge : BlockSourceStep.Fiber (P := P) (L := L) binding
      finalLeft.native.application.base before after)
    (rightEdge : BlockSourceStep.Fiber (P := P) (L := L) binding
      finalRight.native.application.base before after)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex before.plan before.profile leftEdge.beforeCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex before.plan before.profile rightEdge.beforeCurrent right)
    (finalLeftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement (blockIndex + 1) after.plan after.profile
        leftEdge.afterCurrent finalLeft)
    (finalRightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement (blockIndex + 1) after.plan after.profile
        rightEdge.afterCurrent finalRight)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ owner, instruction.submitter = some owner → owner ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (hview : (leftEdge.afterCurrent.current.source.toView focal).eraseEnv =
      (rightEdge.afterCurrent.current.source.toView focal).eraseEnv)
    (hleft : finalLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) left).support)
    (hright : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) right).support) :
    WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal finalLeft finalRight := by
  have hshape := leftEdge.step.profilePoint_next
  change before.next? = some after at hshape
  have leftExtension := leftEdge.step.source_extension
  have rightExtension := rightEdge.step.source_extension
  have hpolled (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
      (hhead : before.plan.instructions deadlineOf = instruction :: rest)
      (owner : P) (howner : instruction.submitter = some owner) : owner ∈ roster :=
    howners instruction (List.mem_of_getElem?
      (leftCheckpoint.instruction_at instruction rest hhead)) owner howner
  have howned (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
      (hhead : before.plan.instructions deadlineOf = instruction :: rest)
      (howner : instruction.submitter = some focal) :=
    leftCheckpoint.owned_block_agreement rightCheckpoint agreement command hpure
      instruction rest hhead howner hroster finalLeft finalRight hleft hright
  obtain ⟨leftCurrent, leftNext, leftStep⟩ := leftEdge
  obtain ⟨rightCurrent, rightNext, rightStep⟩ := rightEdge
  cases before with
  | mk Γ pending prog accounted fresh state plan profile =>
      cases plan with
      | ret => simp [ProfilePoint.next?] at hshape
      | sample next =>
          simp only [ProfilePoint.next?] at hshape
          have hafter := Option.some.inj hshape
          subst after
          have hcontext := (ProfilePoint.of next profile.afterSample).state.wctx
          obtain ⟨leftValue, leftSource⟩ := leftExtension
          obtain ⟨rightValue, rightSource⟩ := rightExtension
          have leftSource := eq_of_heq leftSource
          have rightSource := eq_of_heq rightSource
          have hext := hview
          rw [leftSource, rightSource] at hext
          have hvalue := (VEnv.eraseView_cons_public_recall focal hcontext hext).1
          subst rightValue
          exact WindowedCheckpoint.sample_block_agreement_at_source next profile
            leftCurrent rightCurrent left right finalLeft finalRight
            leftCheckpoint rightCheckpoint agreement command hpure hroster
            leftNext rightNext leftValue leftSource rightSource
            finalLeftCheckpoint.refines finalRightCheckpoint.refines hleft hright
      | @binding Γ pending name owner ty guard tail newName accounted fresh state
          unrestricted next =>
          by_cases howner : owner = focal
          · subst owner
            exact howned _ _ rfl rfl
          · exact WindowedCheckpoint.binding_block_agreement unrestricted next profile
              leftCurrent rightCurrent left right leftCheckpoint rightCheckpoint agreement
              hinitial command hpure hroster (hpolled _ _ rfl owner rfl) howner
              finalLeft finalRight hleft hright
      | @publicChoice Γ pending name publicName owner ty guard tail newName unresolved accounted
          fresh state publicGuard next =>
          simp only [ProfilePoint.next?] at hshape
          have hafter := Option.some.inj hshape
          subst after
          have hcontext := (ProfilePoint.of next profile.afterCommit.afterReveal).state.wctx
          by_cases howner : owner = focal
          · subst owner
            exact howned _ _ rfl rfl
          · obtain ⟨leftValue, leftSource⟩ := leftExtension
            obtain ⟨rightValue, rightSource⟩ := rightExtension
            have leftSource := eq_of_heq leftSource
            have rightSource := eq_of_heq rightSource
            have hext := hview
            rw [leftSource, rightSource] at hext
            have hvalue := (VEnv.eraseView_cons_public_recall focal hcontext hext).1
            subst rightValue
            exact WindowedCheckpoint.publicChoice_block_agreement_at_source
              publicGuard next profile leftCurrent rightCurrent left right finalLeft finalRight
              leftCheckpoint rightCheckpoint agreement hinitial command hpure hroster
              (hpolled _ _ rfl owner rfl) howner leftValue leftNext rightNext
              leftSource rightSource finalLeftCheckpoint.refines finalRightCheckpoint.refines
              hleft hright
      | @conditional Γ pending name publicName owner ty guard tail spec unresolved newName accounted
          fresh state publicGuard next =>
          simp only [ProfilePoint.next?] at hshape
          have hafter := Option.some.inj hshape
          subst after
          have hcontext := (ProfilePoint.of next profile.afterCommit.afterReveal).state.wctx
          by_cases howner : owner = focal
          · subst owner
            exact howned _ _ rfl rfl
          · obtain ⟨leftValue, leftSource⟩ := leftExtension
            obtain ⟨rightValue, rightSource⟩ := rightExtension
            have leftSource := eq_of_heq leftSource
            have rightSource := eq_of_heq rightSource
            have hext := hview
            rw [leftSource, rightSource] at hext
            have hvalue := (VEnv.eraseView_cons_public_recall focal hcontext hext).1
            subst rightValue
            apply WindowedCheckpoint.conditional_block_agreement_at_source
              (.discharge publicGuard next) leftCurrent rightCurrent
              left right finalLeft finalRight leftCheckpoint rightCheckpoint agreement
              hinitial horigins command hpure hroster (hpolled _ _ rfl owner rfl) howner
              (spec.encoding leftValue) leftNext rightNext ?_ ?_
              finalLeftCheckpoint.refines finalRightCheckpoint.refines hleft hright
            · simpa only [Equiv.symm_apply_apply] using leftSource
            · simpa only [Equiv.symm_apply_apply] using rightSource
      | @conditionalCopy Γ pending name publicName owner ty guard tail spec newName unresolved
          accounted fresh state publicGuard next =>
          simp only [ProfilePoint.next?] at hshape
          have hafter := Option.some.inj hshape
          subst after
          have hcontext := (ProfilePoint.of next profile.afterCommit.afterReveal).state.wctx
          by_cases howner : owner = focal
          · subst owner
            exact howned _ _ rfl rfl
          · obtain ⟨leftValue, leftSource⟩ := leftExtension
            obtain ⟨rightValue, rightSource⟩ := rightExtension
            have leftSource := eq_of_heq leftSource
            have rightSource := eq_of_heq rightSource
            have hext := hview
            rw [leftSource, rightSource] at hext
            have hvalue := (VEnv.eraseView_cons_public_recall focal hcontext hext).1
            subst rightValue
            apply WindowedCheckpoint.conditional_block_agreement_at_source
              (.copy publicGuard next) leftCurrent rightCurrent
              left right finalLeft finalRight leftCheckpoint rightCheckpoint agreement
              hinitial horigins command hpure hroster (hpolled _ _ rfl owner rfl) howner
              (spec.encoding leftValue) leftNext rightNext ?_ ?_
              finalLeftCheckpoint.refines finalRightCheckpoint.refines hleft hright
            · simpa only [Equiv.symm_apply_apply] using leftSource
            · simpa only [Equiv.symm_apply_apply] using rightSource

namespace WindowedSourcePrefix

/-- The predecessor and its last edge share one dependent structural index.
Transporting this package preserves the current state and starting execution
used by all of its witnesses. -/
private structure LastStep
    (initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState)
    (blockIndex : Nat) (after : ProfilePoint P L) (sourceNext : after.Coupled)
    (final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (before : ProfilePoint P L) where
  current : before.Coupled
  execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution
  previous : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
    replacement initial blockIndex before.plan before.profile current execution
  block : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
    ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
    (WindowedApplication.blockInvocations roster) execution).support
  source : BlockSourceStep binding final.native.application.base before.plan before.profile current
    after.plan after.profile sourceNext
  checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
    replacement (blockIndex + 1) after.plan after.profile sourceNext final

private theorem lastStep
    {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile prog}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    {blockIndex : Nat}
    (derivation : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement initial (blockIndex + 1) plan profile current final) :
    ∃ before, Nonempty (LastStep (rootProfile := rootProfile) (roster := roster) (focal := focal)
      (replacement := replacement) initial blockIndex (.of plan profile) current final before) := by
  cases derivation with
  | step previous block source checkpoint =>
      exact ⟨.of _ _, ⟨⟨_, _, previous, block, source, checkpoint⟩⟩⟩

/-- At the same source position, equal focal source observations determine
equal runtime policy inputs along all supported initialized block prefixes.
The raw focal replacement is pure but otherwise unrestricted. Every emitted
decision owner is polled; no internal branch-matching premise is assumed. -/
theorem policyAgreement_of_sourceView_eq
    {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ owner, instruction.submitter = some owner → owner ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (blockIndex : Nat) :
    ∀ {point : ProfilePoint P L} {leftCurrent rightCurrent : point.Coupled}
      {left right : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution},
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
        replacement initial blockIndex point.plan point.profile leftCurrent left →
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
        replacement initial blockIndex point.plan point.profile rightCurrent right →
      (leftCurrent.current.source.toView focal).eraseEnv =
        (rightCurrent.current.source.toView focal).eraseEnv →
      WindowedApplication.PolicyAgreement
        (root.windowed deadlineOf binding choice windowOf) focal left right := by
  induction blockIndex with
  | zero =>
      intro point leftCurrent rightCurrent left right leftPrefix rightPrefix hview
      have hleft := leftPrefix.checkpoint.reached
      have hright := rightPrefix.checkpoint.reached
      change left ∈ (FinDist.pure
        (root.windowedInitialExecution deadlineOf binding choice windowOf)).support at hleft
      change right ∈ (FinDist.pure
        (root.windowedInitialExecution deadlineOf binding choice windowOf)).support at hright
      have hleft := FinDist.mem_support_pure.mp hleft
      have hright := FinDist.mem_support_pure.mp hright
      subst left
      subst right
      exact ⟨⟨.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  | succ blockIndex ih =>
      intro point leftCurrent rightCurrent left right leftPrefix rightPrefix hview
      obtain ⟨beforeLeft, ⟨leftLast⟩⟩ := lastStep leftPrefix
      obtain ⟨beforeRight, ⟨rightLast⟩⟩ := lastStep rightPrefix
      have hbefore : beforeLeft = beforeRight :=
        leftLast.previous.profilePoint_eq rightLast.previous
      subst beforeRight
      let leftEdge : BlockSourceStep.Fiber (P := P) (L := L) binding
          left.native.application.base beforeLeft point :=
        ⟨leftLast.current, leftCurrent, leftLast.source⟩
      let rightEdge : BlockSourceStep.Fiber (P := P) (L := L) binding
          right.native.application.base beforeLeft point :=
        ⟨rightLast.current, rightCurrent, rightLast.source⟩
      have hpreviousView := BlockSourceStep.sourceView_recall leftEdge rightEdge focal hview
      have hprevious := ih leftLast.previous rightLast.previous hpreviousView
      exact BlockSourceStep.policyAgreement leftEdge rightEdge leftLast.previous.checkpoint
        rightLast.previous.checkpoint leftLast.checkpoint rightLast.checkpoint
        hinitial horigins hroster howners command hpure hprevious hview
        leftLast.block rightLast.block

end WindowedSourcePrefix
end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.BlockSourceStep.policyAgreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.BlockSourceStep.policyAgreement

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.policyAgreement_of_sourceView_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.policyAgreement_of_sourceView_eq
