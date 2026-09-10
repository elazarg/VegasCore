/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicResolution
import Vegas.Compile.SourceExecutionOutcome
import VegasTests.ApplicationImage

/-! # Public defaults for source bindings

One generated default reads an actual public Boolean input and executes the
original source commitment. A second source site requires equality with a
private Boolean; opposite private environments have identical public views
and disjoint legal choices, so that site admits no public-expression default.
-/

noncomputable section

namespace VegasTests.PublicFallback

open Vegas Vegas.EventGraph Vegas.ToEventGraph
open VegasTests.ApplicationImage

/-- The first mixed-image choice defaults to its existing public input. -/
def publicFallback : SourceDecisionSite.PublicFallback firstSite.decision where
  expr := .var 0 .here
  legal := by
    intro env
    simp [firstSite, firstGuard, evalGuard, evalExpr]
    rfl

/-- The fallback expression is executed from the generated runtime's actual
initial public store and recovers the source input. -/
theorem publicFallback_compiled_eval :
    (publicFallback.compiled source.fresh compilerInitial).evalStore?
        initialState.memory.store = some true := by
  have hresult := publicFallback.compiled_evalStore?_eq_source source.fresh
    compilerInitial (Config.initial compiled.graph).store initialState.memory.store
    source.env (compiledInitialCoupled source).current.agrees
    (fun ref href => initial_represents.publicFields ref
      (publicFallback.compiled_reads_public source.fresh compilerInitial ref href))
  have heval : simpleExpr.eval publicFallback.expr source.env.erasePubEnv = true := by
    change ((VEnv.empty (Player := Fin 2) simpleExpr).cons
      (x := 0) (τ := (.pub BaseTy.bool : BindTy (Fin 2) simpleExpr)) true).erasePubEnv
        0 .bool .here = true
    rfl
  rw [heval] at hresult
  exact hresult

/-- The same value performs the original source commitment step; the fallback
certificate introduces no new source action. -/
theorem publicFallback_source_step :
    SmallStep
      ⟨InitialContext, source.env,
        .commit 1 0 firstGuard firstSite.decision.continuation⟩
      ⟨(1, .sealed 0 .bool) :: InitialContext,
        source.env.cons (simpleExpr.eval publicFallback.expr source.env.erasePubEnv),
        firstSite.decision.continuation⟩ := by
  exact publicFallback.source_step source.env

abbrev PrivateContext : VCtx (Fin 2) simpleExpr := [(0, .sealed 0 .bool)]

def privateGuard :
    Expr ((1, .bool) :: eraseVCtx (viewVCtx (0 : Fin 2) PrivateContext)) .bool :=
  .eq (.var 1 .here) (.var 0 (.there .here))

def privateTail : VegasCore (Fin 2) simpleExpr
    ((1, .sealed 0 .bool) :: PrivateContext) :=
  .reveal 2 0 1 .here
    (.reveal 3 0 0 (.there (.there .here)) (.ret []))

def privateCore : VegasCore (Fin 2) simpleExpr PrivateContext :=
  .commit 1 0 privateGuard privateTail

def privateSite : SourceDecisionSite (0 : Fin 2) privateCore PrivateContext 1 .bool
    privateGuard := by
  change SourceDecisionSite (0 : Fin 2)
    (.commit 1 0 privateGuard privateTail) PrivateContext 1 .bool privateGuard
  exact .here privateGuard privateTail

def privateFalse : VEnv simpleExpr PrivateContext :=
  (VEnv.empty simpleExpr).cons false

def privateTrue : VEnv simpleExpr PrivateContext :=
  (VEnv.empty simpleExpr).cons true

/-- This is a checked source program: both the new commitment and the sealed
initial input are literally revealed before return. Its sealed initial input
is not a claim about the currently supported native initialization slice. -/
def privateSource : GraphProgram (Fin 2) simpleExpr where
  Γ := PrivateContext
  prog := privateCore
  env := privateFalse
  wctx := by simp [PrivateContext, WFCtx]
  fresh := by simp [privateCore, privateTail, FreshBindings, Fresh]

def privateChecked : WFProgram (Fin 2) simpleExpr where
  core := privateSource
  accounted := CommitmentAccounting.ofRevealComplete privateCore privateSource.fresh [0]
    (by simp [PrivateContext]) (by decide)
  legal := by
    unfold privateSource
    unfold privateCore privateTail
    constructor
    · intro env
      exact ⟨env.get .here, by simp [privateGuard, evalGuard, evalExpr]⟩
    · trivial

/-- Opposite private bits require opposite choices, while their public
environments are definitionally identical. Hence no deterministic public
expression is universally legal at this checked source site's first
commitment. -/
theorem no_private_dependent_fallback :
    ¬ Nonempty (SourceDecisionSite.PublicFallback privateSite) := by
  apply SourceDecisionSite.PublicFallback.not_nonempty_of_disjoint_legal
    privateFalse privateTrue rfl
  intro value hfalse htrue
  change (value == false) = true at hfalse
  change (value == true) = true at htrue
  cases value <;> simp at hfalse htrue

end VegasTests.PublicFallback

/-- info: 'VegasTests.PublicFallback.publicFallback_compiled_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PublicFallback.publicFallback_compiled_eval

/-- info: 'VegasTests.PublicFallback.no_private_dependent_fallback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PublicFallback.no_private_dependent_fallback
