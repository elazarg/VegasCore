/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPrefixShape
import Vegas.Compile.WindowedPolicyPrivacy

/-! # Composing block-local information preservation

The whole-prefix argument is independent of the service's invocation layout.
A service must supply the local two-run block law; no source-policy translation
or whole-program outcome law is assumed here.
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
variable {windowOf : Nat → Nat}
variable {service : (root.windowed deadlineOf binding choice windowOf).Service} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}

/-- Block-local comparison at a common structural source edge. Successor
source views determine the branch comparison; target packet equality is not
an assumption. Checkpoints and supported native blocks remain explicit. -/
def BlockSourceStep.PreservesInformation : Prop :=
  ∀
    {before after : ProfilePoint P L} {blockIndex : Nat}
    {left right finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (leftEdge : BlockSourceStep.Fiber (P := P) (L := L) binding
      finalLeft.native.application.base before after)
    (rightEdge : BlockSourceStep.Fiber (P := P) (L := L) binding
      finalRight.native.application.base before after)
    (_ : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      service
      focal replacement blockIndex before.plan before.profile leftEdge.beforeCurrent left)
    (_ : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      service
      focal replacement blockIndex before.plan before.profile rightEdge.beforeCurrent right)
    (_ : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      service
      focal replacement (blockIndex + 1) after.plan after.profile
        leftEdge.afterCurrent finalLeft)
    (_ : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      service
      focal replacement (blockIndex + 1) after.plan after.profile
        rightEdge.afterCurrent finalRight)
    (_ : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (_ : (leftEdge.afterCurrent.current.source.toView focal).eraseEnv =
      (rightEdge.afterCurrent.current.source.toView focal).eraseEnv)
    (_ : finalLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (service.players (root.liftProfile deadlineOf rootProfile) focal replacement)
        service.environment
        service.invocations left).support)
    (_ : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (service.players (root.liftProfile deadlineOf rootProfile) focal replacement)
        service.environment
        service.invocations right).support),
    WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal finalLeft finalRight

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
      service focal
    replacement initial blockIndex before.plan before.profile current execution
  block : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
    (service.players (root.liftProfile deadlineOf rootProfile) focal replacement)
    service.environment
    service.invocations execution).support
  source : BlockSourceStep binding final.native.application.base before.plan before.profile current
    after.plan after.profile sourceNext
  checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      service focal
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
      service
      focal replacement initial (blockIndex + 1) plan profile current final) :
    ∃ before, Nonempty (LastStep (rootProfile := rootProfile) (service := service) (focal := focal)
      (replacement := replacement) initial blockIndex (.of plan profile) current final before) := by
  cases derivation with
  | step previous block source checkpoint =>
      exact ⟨.of _ _, ⟨⟨_, _, previous, block, source, checkpoint⟩⟩⟩

/-- Equal source views determine equal focal runtime inputs along initialized
prefixes whenever each complete block preserves this information relation. -/
theorem policyAgreement_of_sourceView_eq
    {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
    (hstep : BlockSourceStep.PreservesInformation (root := root) (rootProfile := rootProfile)
      (service := service) (focal := focal) (replacement := replacement))
    (blockIndex : Nat) :
    ∀ {point : ProfilePoint P L} {leftCurrent rightCurrent : point.Coupled}
      {left right : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution},
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      service focal
        replacement initial blockIndex point.plan point.profile leftCurrent left →
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      service focal
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
      exact hstep leftEdge rightEdge leftLast.previous.checkpoint
        rightLast.previous.checkpoint leftLast.checkpoint rightLast.checkpoint
        hprevious hview
        leftLast.block rightLast.block

end WindowedSourcePrefix
end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.policyAgreement_of_sourceView_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.policyAgreement_of_sourceView_eq
