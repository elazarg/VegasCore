/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceOutcome

/-! # Source quitting prefixes from compiled public reads

The compiler declares the whole player-visible source context as a decision's
choice footprint.  In particular, every public source binding before that
decision is both in the footprint and public in the completed compiled graph.
Equality on those public choice reads therefore identifies the decoded public
source prefix at the decision.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace SourceDecisionSite

private def publicViewBinding {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (who : P) (binding : VHasVar Γ name (.pub ty)) :
    VHasVar (viewVCtx who Γ) name (.pub ty) := by
  induction Γ with
  | nil => cases binding
  | cons head tail ih =>
      obtain ⟨headName, headTy⟩ := head
      cases binding with
      | here =>
          simp only [viewVCtx, canSee, Visibility.canSee_pub, ↓reduceIte]
          exact .here
      | there binding =>
          unfold viewVCtx
          split
          · exact .there (ih binding)
          · exact ih binding

/-- A public source binding before a decision is one of the compiled guard's
declared choice reads and remains a public typed field reference in the final
compiled graph. -/
theorem publicBinding_choiceRead
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    {query : VarId} {queryTy : L.Ty}
    (binding : HasVar (erasePubVCtx Δ) query queryTy) :
    let siteState := decisionSiteState site fresh state
    let ref : FieldRef L :=
      { field := siteState.fieldOf
          (VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding)),
        ty := queryTy }
    ref ∈ (eventGuardOf siteState who guard).choiceReads ∧
      (compileCore prog fresh state).graph.fieldRefPublic ref := by
  let siteState := decisionSiteState site fresh state
  let publicBinding : VHasVar Δ query (.pub queryTy) :=
    VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding)
  let visible : VHasVar (viewVCtx who Δ) query (.pub queryTy) :=
    publicViewBinding who publicBinding
  have hsame : VHasVar.ofViewVCtx visible = publicBinding :=
    HasVar.eq_of_nodup siteState.wctx _ _
  have hmem := fieldRefOfView_mem_visibleFieldRefs siteState who visible
  have hchoice :
      ({ field := siteState.fieldOf publicBinding, ty := queryTy } : FieldRef L) ∈
        (eventGuardOf siteState who guard).choiceReads := by
    simpa only [eventGuardOf, BuildState.fieldRefOfView, hsame] using hmem
  refine ⟨hchoice, ?_⟩
  obtain ⟨spec, hfield, htype, howner⟩ := siteState.fieldOf_spec publicBinding
  refine ⟨spec, ?_, htype, howner⟩
  rw [← decisionSiteState_field?_eq_compileCore site fresh state]
  · exact hfield
  · exact siteState.fieldOf_lt publicBinding

/-- Equality on the public part of a compiled decision's choice footprint
identifies the public source environment recorded before that decision in two
decoded terminal configurations. -/
theorem recorded_tail_erasePubEnv_eq_of_choiceReads_eq
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (left right : ReachableConfig (compileCore prog fresh state).graph)
    (hleft : Terminal (compileCore prog fresh state).graph left.1)
    (hright : Terminal (compileCore prog fresh state).graph right.1)
    (hagrees : ∀ ref,
      ref ∈ (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads →
      (compileCore prog fresh state).graph.fieldRefPublic ref →
      Store.getAs left.1.store ref.field ref.ty =
        Store.getAs right.1.store ref.field ref.ty) :
    (site.recorded (decodeSourceOutcome prog fresh state left hleft)).tail.erasePubEnv =
      (site.recorded (decodeSourceOutcome prog fresh state right hright)).tail.erasePubEnv := by
  apply site.recorded_tail_erasePubEnv_eq_of_getAs_eq fresh state left right hleft hright
  intro query queryTy binding
  let ref : FieldRef L :=
    { field := (decisionSiteState site fresh state).fieldOf
        (VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding)),
      ty := queryTy }
  have hread := site.publicBinding_choiceRead fresh state binding
  exact hagrees ref hread.1 hread.2

end SourceDecisionSite

end Vegas

/-- info: 'Vegas.SourceDecisionSite.recorded_tail_erasePubEnv_eq_of_choiceReads_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.recorded_tail_erasePubEnv_eq_of_choiceReads_eq
