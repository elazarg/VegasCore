/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceBacktranslation

/-! # Source bindings for public graph-prefix fields

Every public node emitted before a source decision retains a public source
binding. This coverage complements allocation injectivity: it is the direction
needed to read earlier disclosures when backtranslating a native policy.
-/

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

def BuildState.PublicNodeBindings {Γ : VCtx P L} (state : BuildState P L Γ) : Prop :=
  ∀ index event, state.nodes[index]? = some event → event.owner = none →
    ∃ name, ∃ binding : VHasVar Γ name (.pub event.ty),
      state.fieldOf binding = state.initialFields.length + index

theorem BuildState.fromInitial_publicNodeBindings {Γ : VCtx P L}
    (state : InitialState P L Γ) : (BuildState.fromInitial state).PublicNodeBindings := by
  intro index event hget
  simp only [fromInitial, List.getElem?_nil, reduceCtorEq] at hget

theorem BuildState.addEvent_publicNodeBindings {Γ : VCtx P L}
    (state : BuildState P L Γ) (hcovered : state.PublicNodeBindings)
    (name : VarId) (bindTy : BindTy P L) (sem : NodeSem P L) (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
          [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem }) :
    (state.addEvent name bindTy sem hfresh hnode).1.PublicNodeBindings := by
  intro index event hget hpublic
  change (state.nodes ++ [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }])[index]? =
    some event at hget
  by_cases hbefore : index < state.nodes.length
  · rw [List.getElem?_append_left hbefore] at hget
    obtain ⟨oldName, binding, hfield⟩ := hcovered index event hget hpublic
    exact ⟨oldName, .there binding, hfield⟩
  · have hindex : index = state.nodes.length := by
      obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hget
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    subst index
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hget
    subst event
    obtain ⟨base, visibility⟩ := bindTy
    cases visibility with
    | pub => exact ⟨name, .here, rfl⟩
    | sealed owner => cases hpublic

theorem decisionSiteState_publicNodeBindings
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hcovered : state.PublicNodeBindings) :
    (decisionSiteState site fresh state).PublicNodeBindings := by
  induction site with
  | here => exact hcovered
  | sample site ih =>
      apply ih fresh.2
      unfold BuildState.addSampleEvent
      exact state.addEvent_publicNodeBindings hcovered _ _ _ _ _
  | commit site ih =>
      apply ih fresh.2
      unfold BuildState.addCommitEvent
      exact state.addEvent_publicNodeBindings hcovered _ _ _ _ _
  | reveal site ih =>
      apply ih fresh.2
      unfold BuildState.addRevealEvent
      exact state.addEvent_publicNodeBindings hcovered _ _ _ _ _

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

theorem BuildState.publicNode_mem_visibleFieldRefs {Γ : VCtx P L}
    (state : BuildState P L Γ) (hcovered : state.PublicNodeBindings)
    (who : P) (index : Nat) (event : EventNode P L)
    (hget : state.nodes[index]? = some event) (hpublic : event.owner = none) :
    { field := state.initialFields.length + index, ty := event.ty } ∈
      visibleFieldRefs state who := by
  obtain ⟨name, binding, hfield⟩ := hcovered index event hget hpublic
  let visible := publicViewBinding who binding
  have hsame : visible.ofViewVCtx = binding := HasVar.eq_of_nodup state.wctx _ _
  have hmem := fieldRefOfView_mem_visibleFieldRefs state who visible
  simpa only [BuildState.fieldRefOfView, hsame, hfield] using hmem

/-- Every source-earlier public graph output belongs to a compiled source
choice's declared reads, including a disclosure received early in the pool. -/
theorem compile_commit_prior_public_read (program : GraphProgram P L)
    (who : P) (node prior : Fin (compile program).graph.nodeCount) (guard : EventGuard L)
    (hsem : ((compile program).graph.nodeRow node).sem = .commit who guard)
    (hbefore : prior.val < node.val)
    (hpublic : ((compile program).graph.nodeRow prior).owner = none) :
    { field := (compile program).graph.nodeTarget prior,
      ty := ((compile program).graph.nodeRow prior).ty } ∈ guard.choiceReads := by
  let state := BuildState.fromInitial (initialState program.Γ program.env program.wctx)
  let result := compileCore program.prog program.fresh state
  obtain ⟨actor, Δ, name, ty, sourceGuard, site, hindex, hrow⟩ :=
    compileCore_commitNode_covered program.prog program.fresh state node
      (by simp [state]) ⟨result.graph.nodeRow node, who, guard,
        result.graph.nodes_get?_nodeRow node, hsem⟩
  have hrowEq := Option.some.inj ((result.graph.nodes_get?_nodeRow node).symm.trans hrow)
  have hcommit := hsem.symm.trans (congrArg EventNode.sem hrowEq)
  have hactor := (NodeSem.commit.inj hcommit).1
  subst actor
  have hguard := (NodeSem.commit.inj hcommit).2
  subst guard
  let siteState := decisionSiteState site program.fresh state
  have hcovered := decisionSiteState_publicNodeBindings site program.fresh state
    (BuildState.fromInitial_publicNodeBindings _)
  have hget : siteState.nodes[prior.val]? = some (result.graph.nodeRow prior) := by
    have hfull := result.graph.nodes_get?_nodeRow prior
    obtain ⟨suffix, hsuffix⟩ := decisionSiteState_nodes_prefix site program.fresh state
    change result.nodes[prior.val]? = some _ at hfull
    have hlt : prior.val < siteState.nodes.length := by
      change prior.val < (decisionSiteState site program.fresh state).nodes.length
      omega
    rw [← hsuffix, List.getElem?_append_left hlt] at hfull
    exact hfull
  have hmem := siteState.publicNode_mem_visibleFieldRefs hcovered who prior.val
    (result.graph.nodeRow prior) hget hpublic
  simpa only [eventGuardOf, Graph.nodeTarget, BuildResult.graph,
    compile, compileCore_initialFields, decisionSiteState_initialFields, siteState,
    result] using hmem

end Vegas.ToEventGraph
