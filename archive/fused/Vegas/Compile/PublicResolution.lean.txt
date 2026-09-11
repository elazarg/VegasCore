/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceLaw
import Vegas.Compile.DecisionSite

/-! # Source-authorized public fallbacks

A public fallback is a typed public source expression whose value satisfies
one source decision guard at every source environment. It authorizes an
operational fallback value; it does not identify the owner's behavioral
choice, assert frontend quitting intent, or contain a runtime or terminal-law
premise.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Runtime evaluation against a public store recovers exactly the source
value. The represented store/source relation and the public-store projection
are separate premises, so no proof-only source environment enters execution. -/
theorem eventExprOf_evalStore?_eq_source
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ) (expr : L.Expr (erasePubVCtx Γ) ty)
    (representedStore publicStore : Store L) (source : VEnv L Γ)
    (hrepresents : state.Agrees representedStore source)
    (hpublic : ∀ ref, ref ∈ (eventExprOf state expr).reads →
      Store.getAs publicStore ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty) :
    (eventExprOf state expr).evalStore? publicStore =
      some (L.eval expr source.erasePubEnv) := by
  let available : ∀ ref, ref ∈ (eventExprOf state expr).reads →
      ∃ value, Store.getAs publicStore ref.field ref.ty = some value := by
    intro ref href
    rw [hpublic _ href]
    exact exprReadRefs_store_available state representedStore
      (fun binding => ⟨source.get binding, hrepresents binding⟩) expr ref href
  let reads := ReadEnv.ofStore publicStore (eventExprOf state expr).reads available
  have hreads : ReadEnv.ofStore? publicStore (eventExprOf state expr).reads = some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos available]
  have hreadsExec : ReadEnv.ofStoreExec? publicStore
      (eventExprOf state expr).reads = some reads :=
    ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some hreads
  unfold EventExpr.evalStore?
  rw [hreadsExec, Option.map_some]
  apply congrArg some
  apply eventExprOf_eval_eq_eval state expr source.erasePubEnv reads
  intro name depTy binding dependency
  have href := exprReadRefs_mem state expr binding dependency
  have hread := ReadEnv.ofStore?_read hreads href
  have hrepresented := hrepresents
    (VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding))
  apply Option.some.inj
  change some (sourceValuePub state reads binding href) =
    some (source.erasePubEnv name depTy binding)
  exact hread.symm.trans ((hpublic _ href).trans (by
    simpa [BuildState.fieldRefOfPub, BuildState.fieldOfPub,
      VEnv.erasePubEnv_get, VEnv.get] using hrepresented))

namespace SourceDecisionSite

/-- A public expression that supplies a legal value of one source decision in
every environment at that occurrence. -/
structure PublicFallback
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard) where
  expr : L.Expr (erasePubVCtx Δ) ty
  legal : ∀ env : VEnv L Δ,
    evalGuard guard (L.eval expr env.erasePubEnv)
      ((env.toView who).eraseEnv) = true

namespace PublicFallback

/-- Executable expression code at the compiler cursor immediately preceding
the annotated source decision. -/
def compiled
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : PublicFallback site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) : EventExpr L ty :=
  eventExprOf (decisionSiteState site fresh build) fallback.expr

/-- Every generated fallback dependency is a public field of the final
compiled graph. -/
theorem compiled_reads_public
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : PublicFallback site)
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
    (fallback : PublicFallback site)
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

/-- The authorized fallback is an actual step of the original source
decision, not a decoder-invented value or a new source action. -/
theorem source_step
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : PublicFallback site) (env : VEnv L Δ) :
    SmallStep
      ⟨Δ, env, .commit name who guard site.continuation⟩
      ⟨(name, .sealed who ty) :: Δ,
        env.cons (L.eval fallback.expr env.erasePubEnv), site.continuation⟩ :=
  .commit guard site.continuation _ (fallback.legal env)

/-- If two environments with identical public information have no common
legal decision value, no deterministic public-expression fallback covers
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
    ¬ Nonempty (PublicFallback site) := by
  rintro ⟨fallback⟩
  let value := L.eval fallback.expr left.erasePubEnv
  apply hdisjoint value (fallback.legal left)
  simpa only [value, ← hpublic] using fallback.legal right

end PublicFallback
end SourceDecisionSite
end Vegas

/-- info: 'Vegas.eventExprOf_evalStore?_eq_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.eventExprOf_evalStore?_eq_source

/-- info: 'Vegas.SourceDecisionSite.PublicFallback.compiled_reads_public' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.PublicFallback.compiled_reads_public

/-- info: 'Vegas.SourceDecisionSite.PublicFallback.compiled_evalStore?_eq_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.PublicFallback.compiled_evalStore?_eq_source
