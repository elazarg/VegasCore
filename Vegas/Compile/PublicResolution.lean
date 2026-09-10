/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceImage
import Vegas.Compile.SourceLaw

/-! # Source-authorized public resolution choices

A resolution annotation retains one typed public source expression and proves
that its value is legal at the annotated source occurrence.  It authorizes a
backend fallback; it does not say that the source owner's behavioral policy
would have selected that value, and it contains no terminal-law premise.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Runtime evaluation against a public store recovers exactly the source
value.  The represented store/source relation and the public-store projection
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

/-- An explicit backend resolution value for one adjacent public source
choice.  Universally quantified source legality makes timeout resolution total
at every environment in which this source occurrence is reached. -/
structure PublicResolutionChoice {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) where
  expr : L.Expr (erasePubVCtx site.context) site.ty
  legal : ∀ env : VEnv L site.context,
    evalGuard site.guard (L.eval expr env.erasePubEnv)
      ((env.toView site.owner).eraseEnv) = true

namespace PublicResolutionChoice

/-- Executable typed expression code for this resolution annotation. -/
def compiled {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) : EventExpr L site.ty :=
  eventExprOf (site.siteState fresh state) resolution.expr

/-- Every retained resolution-expression dependency is a public field of the
final compiled graph.  This is a consequence of the source expression's
public context and decision-site prefix preservation, not a runtime premise. -/
theorem compiled_reads_public
    {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    ∀ ref, ref ∈ (resolution.compiled fresh state).reads →
      (compileCore prog fresh state).graph.fieldRefPublic ref := by
  intro ref href
  have hlocal := exprReadRefs_public (site.siteState fresh state)
    resolution.expr ref href
  rcases hlocal with ⟨spec, hfield, hty, howner⟩
  refine ⟨spec, ?_, hty, howner⟩
  rw [← decisionSiteState_field?_eq_compileCore site.decision fresh state
    ref.field ?_]
  · exact hfield
  · have hlt :=
      ({ initialFields := (site.siteState fresh state).initialFields,
         nodes := (site.siteState fresh state).nodes } :
        EventGraph.Graph P L).field_lt_fieldCount_of_field?_some hfield
    simpa only [PublicChoiceSite.siteState, EventGraph.Graph.fieldCount,
      EventGraph.Graph.nodeCount] using hlt

/-- A resolution choice performs the original adjacent source commit and
reveal; it is not a new source transition. -/
theorem source_steps {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (env : VEnv L site.context) :
    SmallStep.Star
      ⟨site.context, env,
        .commit site.choiceName site.owner site.guard site.decision.continuation⟩
      ⟨(site.publicName, .pub site.ty) ::
          (site.choiceName, .sealed site.owner site.ty) :: site.context,
        (env.cons (L.eval resolution.expr env.erasePubEnv)).cons
          (L.eval resolution.expr env.erasePubEnv), site.tail⟩ :=
  site.completePublication_source_steps env
    (L.eval resolution.expr env.erasePubEnv) (resolution.legal env)

/-- The emitted public expression evaluates to the certified source value
under represented/public store agreement. -/
theorem compiled_evalStore?_eq_source
    {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (representedStore publicStore : Store L) (env : VEnv L site.context)
    (hrepresents : (site.siteState fresh state).Agrees representedStore env)
    (hpublic : ∀ ref, ref ∈ (resolution.compiled fresh state).reads →
      Store.getAs publicStore ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty) :
    (resolution.compiled fresh state).evalStore? publicStore =
      some (L.eval resolution.expr env.erasePubEnv) :=
  eventExprOf_evalStore?_eq_source (site.siteState fresh state) resolution.expr
    representedStore publicStore env hrepresents hpublic

end PublicResolutionChoice

end Vegas

/-- info: 'Vegas.eventExprOf_evalStore?_eq_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.eventExprOf_evalStore?_eq_source

/-- info: 'Vegas.PublicResolutionChoice.compiled_reads_public' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicResolutionChoice.compiled_reads_public

/-- info: 'Vegas.PublicResolutionChoice.source_steps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicResolutionChoice.source_steps
