/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourcePrefix

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

end ProfilePoint

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
