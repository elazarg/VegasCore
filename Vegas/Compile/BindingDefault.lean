/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicResolution

/-! # Source-authorized defaults for opaque bindings

A binding default is a typed public source expression whose value satisfies
the original commitment guard at every source environment. It authorizes an
operational fallback value; it does not identify the owner's behavioral
choice, assert that the frontend intended quitting, or contain a runtime or
terminal-law premise.
-/

noncomputable section

namespace Vegas.SourceDecisionSite

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A public expression that is a legal value of one source commitment in
every environment at that occurrence. -/
structure BindingDefault
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard) where
  expr : L.Expr (erasePubVCtx Δ) ty
  legal : ∀ env : VEnv L Δ,
    evalGuard guard (L.eval expr env.erasePubEnv)
      ((env.toView who).eraseEnv) = true

namespace BindingDefault

/-- Executable expression code at the compiler cursor immediately preceding
the annotated source commitment. -/
def compiled
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : BindingDefault site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) : EventExpr L ty :=
  eventExprOf (decisionSiteState site fresh build) fallback.expr

/-- Every generated fallback dependency is a public field of the final
compiled graph. -/
theorem compiled_reads_public
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : BindingDefault site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) :
    ∀ ref, ref ∈ (fallback.compiled fresh build).reads →
      (compileCore prog fresh build).graph.fieldRefPublic ref := by
  intro ref href
  let current := decisionSiteState site fresh build
  have hlocal := exprReadRefs_public current fallback.expr ref href
  rcases hlocal with ⟨spec, hfield, htype, howner⟩
  refine ⟨spec, ?_, htype, howner⟩
  rw [← decisionSiteState_field?_eq_compileCore site fresh build ref.field ?_]
  · exact hfield
  · have hlt :=
      ({ initialFields := current.initialFields, nodes := current.nodes } :
        Graph P L).field_lt_fieldCount_of_field?_some hfield
    simpa only [Graph.fieldCount, Graph.nodeCount, current] using hlt

/-- Executing the generated fallback expression from matching public runtime
reads yields its exact source value. -/
theorem compiled_evalStore?_eq_source
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : BindingDefault site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (representedStore publicStore : Store L) (env : VEnv L Δ)
    (hrepresents : (decisionSiteState site fresh build).Agrees representedStore env)
    (hpublic : ∀ ref, ref ∈ (fallback.compiled fresh build).reads →
      Store.getAs publicStore ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty) :
    (fallback.compiled fresh build).evalStore? publicStore =
      some (L.eval fallback.expr env.erasePubEnv) :=
  eventExprOf_evalStore?_eq_source (decisionSiteState site fresh build)
    fallback.expr representedStore publicStore env hrepresents hpublic

/-- The authorized default is an actual step of the original source
commitment, not a decoder-invented value or a new source action. -/
theorem source_step
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : BindingDefault site) (env : VEnv L Δ) :
    SmallStep
      ⟨Δ, env, .commit name who guard site.continuation⟩
      ⟨(name, .sealed who ty) :: Δ,
        env.cons (L.eval fallback.expr env.erasePubEnv), site.continuation⟩ :=
  .commit guard site.continuation _ (fallback.legal env)

/-- If two environments with identical public information have no common
legal commitment value, no deterministic public-expression default can cover
both. -/
theorem not_nonempty_of_disjoint_legal
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (left right : VEnv L Δ)
    (hpublic : left.erasePubEnv = right.erasePubEnv)
    (hdisjoint : ∀ value : L.Val ty,
      evalGuard guard value ((left.toView who).eraseEnv) = true →
      evalGuard guard value ((right.toView who).eraseEnv) = true → False) :
    ¬ Nonempty (BindingDefault site) := by
  rintro ⟨fallback⟩
  let value := L.eval fallback.expr left.erasePubEnv
  apply hdisjoint value (fallback.legal left)
  simpa only [value, ← hpublic] using fallback.legal right

end BindingDefault

end Vegas.SourceDecisionSite

/-- info: 'Vegas.SourceDecisionSite.BindingDefault.compiled_reads_public' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.BindingDefault.compiled_reads_public

/-- info: 'Vegas.SourceDecisionSite.BindingDefault.compiled_evalStore?_eq_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.BindingDefault.compiled_evalStore?_eq_source
