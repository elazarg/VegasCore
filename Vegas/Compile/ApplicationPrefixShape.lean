/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourcePrefix
import Vegas.Core.SourceRecall

/-! # Deterministic structural positions in an application plan -/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable (P : Type) [DecidableEq P] (L : IExpr)

/-- A dependent package for one plan/profile position. It deliberately omits
source environments and runtime states: advancing it is purely structural. -/
structure ProfilePoint where
  context : VCtx P L
  pending : Finset VarId
  program : VegasCore P L context
  accounted : CommitmentAccounting pending program
  fresh : FreshBindings program
  state : BuildState P L context
  plan : ApplicationPlan accounted fresh state
  profile : SourceBehavioralProfile program

namespace ProfilePoint

variable {P : Type} [DecidableEq P] {L : IExpr}

def of {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog) : ProfilePoint P L :=
  ⟨Γ, pending, prog, accounted, fresh, state, plan, profile⟩

/-- The unique structural successor of a nonterminal application-plan point. -/
def next? (point : ProfilePoint P L) : Option (ProfilePoint P L) :=
  match point with
  | ⟨_, _, _, _, _, _, plan, profile⟩ =>
      match plan with
      | .ret _ _ _ => none
      | .sample next => some (.of next profile.afterSample)
      | .binding _ next => some (.of next profile.afterCommit)
      | .publicChoice _ next => some (.of next profile.afterCommit.afterReveal)
      | .conditional _ next => some (.of next profile.afterCommit.afterReveal)
      | .conditionalCopy _ _ next => some (.of next profile.afterCommit.afterReveal)

/-- Iterate the deterministic structural successor. The recursion order makes
the induction step consume the already established prefix position. -/
def after : Nat → ProfilePoint P L → Option (ProfilePoint P L)
  | 0, point => some point
  | n + 1, point => (after n point).bind next?

/-- The source checkpoint type at a packaged structural position. -/
abbrev Coupled (point : ProfilePoint P L) :=
  CoupledAt (compileCore point.program point.fresh point.state).graph point.state

/-- The source-environment extension shape selected by this plan head. This
forgets support and legality evidence while retaining the typed written-order
extension needed for dependent inversion. -/
def SourceExtension (point : ProfilePoint P L) {Δ : VCtx P L}
    (source : VEnv L point.context) (nextSource : VEnv L Δ) : Prop :=
  match point with
  | ⟨_, _, _, _, _, _, plan, _⟩ =>
      match plan with
      | .ret _ _ _ => False
      | @ApplicationPlan.sample _ _ _ _ _ name ty _ _ _ _ _ _ =>
          ∃ value : L.Val ty, HEq nextSource
            (source.cons (x := name) (τ := .pub ty) value)
      | @ApplicationPlan.binding _ _ _ _ _ name owner ty _ _ _ _ _ _ _ _ =>
          ∃ value : L.Val ty, HEq nextSource
            (source.cons (x := name) (τ := .sealed owner ty) value)
      | @ApplicationPlan.publicChoice _ _ _ _ _ name publicName owner ty _ _ _ _ _ _ _ _ _ =>
          ∃ value : L.Val ty, HEq nextSource
            ((source.cons (x := name) (τ := .sealed owner ty) value).cons
              (x := publicName) (τ := .pub ty) value)
      | @ApplicationPlan.conditional _ _ _ _ _ name publicName owner ty _ _ _ _ _ _ _ _ _ _ =>
          ∃ value : L.Val ty, HEq nextSource
            ((source.cons (x := name) (τ := .sealed owner ty) value).cons
              (x := publicName) (τ := .pub ty) value)
      | @ApplicationPlan.conditionalCopy _ _ _ _ _ name publicName owner ty _ _ _ _ _ _ _ _
          _ _ =>
          ∃ value : L.Val ty, HEq nextSource
            ((source.cons (x := name) (τ := .sealed owner ty) value).cons
              (x := publicName) (τ := .pub ty) value)

end ProfilePoint

/-- A source edge packaged over its structural endpoints. Reindexing this
whole fiber transports all dependent compiler indices together. -/
structure BlockSourceStep.Fiber
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (final : ApplicationImage.State P L) (before after : ProfilePoint P L) where
  beforeCurrent : before.Coupled
  afterCurrent : after.Coupled
  step : BlockSourceStep binding final before.plan before.profile beforeCurrent
    after.plan after.profile afterCurrent

namespace BlockSourceStep.Fiber

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {final : ApplicationImage.State P L}

/-- Transport a complete source-edge fiber along equal structural endpoints. -/
def cast {before₁ before₂ after₁ after₂ : ProfilePoint P L}
    (hbefore : before₁ = before₂) (hafter : after₁ = after₂)
    (edge : BlockSourceStep.Fiber (P := P) (L := L) binding final before₁ after₁) :
    BlockSourceStep.Fiber (P := P) (L := L) binding final before₂ after₂ := by
  subst before₂
  subst after₂
  exact edge

end BlockSourceStep.Fiber

namespace BlockSourceStep

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A source edge follows the deterministic plan/profile successor. -/
theorem profilePoint_next
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {final : ApplicationImage.State P L}
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    {plan : ApplicationPlan accounted fresh state}
    {nextPlan : ApplicationPlan nextAccounted nextFresh nextState}
    {profile : SourceBehavioralProfile prog} {nextProfile : SourceBehavioralProfile nextProg}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {sourceNext : CoupledAt (compileCore nextProg nextFresh nextState).graph nextState}
    (source : BlockSourceStep binding final plan profile current nextPlan nextProfile sourceNext) :
    ProfilePoint.next? (.of plan profile) = some (.of nextPlan nextProfile) := by
  cases source <;> rfl

/-- Every source step exposes the typed environment-extension shape of its
plan head without dependent elimination against another edge. -/
theorem source_extension
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {final : ApplicationImage.State P L}
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    {plan : ApplicationPlan accounted fresh state}
    {nextPlan : ApplicationPlan nextAccounted nextFresh nextState}
    {profile : SourceBehavioralProfile prog} {nextProfile : SourceBehavioralProfile nextProg}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {sourceNext : CoupledAt (compileCore nextProg nextFresh nextState).graph nextState}
    (source : BlockSourceStep binding final plan profile current nextPlan nextProfile sourceNext) :
    ProfilePoint.SourceExtension (.of plan profile) current.current.source
      sourceNext.current.source := by
  cases source with
  | sample value draw hsource | binding _ _ _ value hsource _
  | publicChoice value hsource _ =>
      rw [hsource]
      exact ⟨value, HEq.rfl⟩
  | conditional result admissible hsource legal
  | conditionalCopy result admissible hsource legal =>
      rw [hsource]
      exact ⟨_, HEq.rfl⟩

/-- Aligned source edges recall equality of the focal source view before the
edge. The edge descriptor avoids dependent elimination over accounting
proofs whose `erase` indices are not injective. -/
theorem sourceView_recall
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {leftFinal rightFinal : ApplicationImage.State P L}
    {before after : ProfilePoint P L}
    (left : BlockSourceStep.Fiber (P := P) (L := L) binding leftFinal before after)
    (right : BlockSourceStep.Fiber (P := P) (L := L) binding rightFinal before after)
    (focal : P)
    (hview : (left.afterCurrent.current.source.toView focal).eraseEnv =
      (right.afterCurrent.current.source.toView focal).eraseEnv) :
    (left.beforeCurrent.current.source.toView focal).eraseEnv =
      (right.beforeCurrent.current.source.toView focal).eraseEnv := by
  have hcontext := after.state.wctx
  obtain ⟨leftCurrent, leftNext, leftStep⟩ := left
  obtain ⟨rightCurrent, rightNext, rightStep⟩ := right
  have hshape : before.next? = some after := leftStep.profilePoint_next
  have leftExtension := leftStep.source_extension
  have rightExtension := rightStep.source_extension
  cases before with
  | mk Γ pending prog accounted fresh state plan profile =>
      cases plan with
      | ret => simp [ProfilePoint.next?] at hshape
      | sample next | binding _ next =>
          simp only [ProfilePoint.next?, Option.some.injEq] at hshape
          subst after
          simp only [ProfilePoint.SourceExtension] at leftExtension rightExtension
          obtain ⟨leftValue, leftSource⟩ := leftExtension
          obtain ⟨rightValue, rightSource⟩ := rightExtension
          have leftSource := eq_of_heq leftSource
          have rightSource := eq_of_heq rightSource
          rw [leftSource, rightSource] at hview
          exact VEnv.eraseView_cons_recall focal hcontext hview
      | publicChoice _ next | conditional _ next | conditionalCopy _ _ next =>
          simp only [ProfilePoint.next?, Option.some.injEq] at hshape
          subst after
          simp only [ProfilePoint.SourceExtension] at leftExtension rightExtension
          obtain ⟨leftValue, leftSource⟩ := leftExtension
          obtain ⟨rightValue, rightSource⟩ := rightExtension
          have leftSource := eq_of_heq leftSource
          have rightSource := eq_of_heq rightSource
          rw [leftSource, rightSource] at hview
          have htail := VEnv.eraseView_cons_recall focal hcontext hview
          exact VEnv.eraseView_cons_recall focal hcontext.tail htail

end BlockSourceStep

namespace WindowedSourcePrefix

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext : VCtx P L} {rootPending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}

/-- Every actual windowed source prefix lies at the deterministic structural
plan/profile position selected by its block count. -/
theorem profilePoint_after
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
    {windowOf : Nat → Nat} {roster : List P} {focal : P}
    {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
    {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} {blockIndex : Nat}
    {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile prog}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {execution : (root.windowed deadlineOf binding choice
      windowOf).application.PolicyExecution}
    (derivation : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster
      focal replacement initial blockIndex plan profile current execution) :
    ProfilePoint.after blockIndex (.of root rootProfile) = some (.of plan profile) := by
  induction derivation with
  | initial => rfl
  | step previous block source checkpoint ih =>
      simp only [ProfilePoint.after, ih, Option.bind_some]
      cases source <;> rfl

/-- Two actual prefixes from the same root and at the same block count have
the same dependent plan/profile package. This is useful before eliminating
their final source steps, whose predecessor indices are otherwise unrelated. -/
theorem profilePoint_eq
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
    {windowOf : Nat → Nat} {roster : List P} {focal : P}
    {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
    {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
    {leftΓ rightΓ : VCtx P L} {leftPending rightPending : Finset VarId}
    {leftProg : VegasCore P L leftΓ} {rightProg : VegasCore P L rightΓ}
    {leftAccounted : CommitmentAccounting leftPending leftProg}
    {rightAccounted : CommitmentAccounting rightPending rightProg}
    {leftFresh : FreshBindings leftProg} {rightFresh : FreshBindings rightProg}
    {leftState : BuildState P L leftΓ} {rightState : BuildState P L rightΓ}
    {blockIndex : Nat}
    {leftPlan : ApplicationPlan leftAccounted leftFresh leftState}
    {rightPlan : ApplicationPlan rightAccounted rightFresh rightState}
    {leftProfile : SourceBehavioralProfile leftProg}
    {rightProfile : SourceBehavioralProfile rightProg}
    {leftCurrent : CoupledAt (compileCore leftProg leftFresh leftState).graph leftState}
    {rightCurrent : CoupledAt (compileCore rightProg rightFresh rightState).graph rightState}
    {left right : (root.windowed deadlineOf binding choice
      windowOf).application.PolicyExecution}
    (leftPrefix : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster
      focal replacement initial blockIndex leftPlan leftProfile leftCurrent left)
    (rightPrefix : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster
      focal replacement initial blockIndex rightPlan rightProfile rightCurrent right) :
    ProfilePoint.of leftPlan leftProfile = ProfilePoint.of rightPlan rightProfile := by
  exact Option.some.inj
    (leftPrefix.profilePoint_after.symm.trans rightPrefix.profilePoint_after)

end WindowedSourcePrefix
end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.profilePoint_after'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.profilePoint_after

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.profilePoint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.profilePoint_eq

/-- info: 'Vegas.ApplicationPlan.BlockSourceStep.source_extension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.BlockSourceStep.source_extension

/-- info: 'Vegas.ApplicationPlan.BlockSourceStep.sourceView_recall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.BlockSourceStep.sourceView_recall
