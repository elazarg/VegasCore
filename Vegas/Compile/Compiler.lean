/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.WellFormed.Program
import Vegas.EventGraph.Build

/-!
# Core-to-event-graph compiler

Checked programs compile directly to canonical event graphs.  The compiler
state is indexed by the current source context, so source-variable lookup is
proof-bearing: there is no default field id for a missing variable.
-/

namespace Vegas

namespace ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Recover a typed `HasVar` proof from name membership in a plain context. -/
private noncomputable def hasVarOfNameMem
    {Γ : Ctx L.Ty} {name : VarId}
    (hctx : (Γ.map Prod.fst).Nodup)
    (hmem : name ∈ Γ.map Prod.fst) :
    Σ ty, HasVar Γ name ty :=
  match Γ with
  | [] => by
      simp at hmem
  | (headName, headTy) :: tail =>
      if hname : name = headName then
        ⟨headTy, by subst name; exact HasVar.here⟩
      else
        let tailVar :=
          hasVarOfNameMem (Γ := tail) (name := name)
            (List.nodup_cons.mp hctx).2
            (by
              simpa [hname] using hmem)
        ⟨tailVar.1, HasVar.there tailVar.2⟩

/-- Initial-field compiler accumulator. It exists only before body events are
allocated, so appending an initial field cannot shift any event field ids. -/
structure InitialState (P : Type) [DecidableEq P] (L : IExpr)
    (Γ : VCtx P L) where
  initialFields : List (InitialField P L)
  wctx : WFCtx Γ
  fieldOf : {name : VarId} → {bindTy : BindTy P L} →
    VHasVar Γ name bindTy → Nat
  fieldOf_spec :
    ∀ {name : VarId} {bindTy : BindTy P L}
      (h : VHasVar Γ name bindTy),
        ∃ spec, initialFields[fieldOf h]? = some spec ∧
          spec.ty = bindTy.base ∧ spec.owner = bindTy.owner

namespace InitialState

variable {Γ : VCtx P L}

def empty : InitialState P L [] where
  initialFields := []
  wctx := WFCtx_nil
  fieldOf := by
    intro _ _ h
    cases h
  fieldOf_spec := by
    intro _ _ h
    cases h

def nextField (state : InitialState P L Γ) : Nat :=
  state.initialFields.length

theorem fieldOf_lt (state : InitialState P L Γ)
    {name : VarId} {bindTy : BindTy P L}
    (h : VHasVar Γ name bindTy) :
    state.fieldOf h < state.initialFields.length := by
  rcases state.fieldOf_spec h with ⟨_spec, hget, _hty, _howner⟩
  exact (List.getElem?_eq_some_iff.mp hget).1

def consFieldOf (state : InitialState P L Γ) (field : Nat)
    {name : VarId} {bindTy : BindTy P L} :
    {query : VarId} → {queryTy : BindTy P L} →
      VHasVar ((name, bindTy) :: Γ) query queryTy → Nat
  | _, _, .here => field
  | _, _, .there htail => state.fieldOf htail

/-- Extend the initial context with one source field. -/
def addField (state : InitialState P L Γ)
    (name : VarId) (bindTy : BindTy P L)
    (value : L.Val bindTy.base) (hfresh : Fresh name Γ) :
    InitialState P L ((name, bindTy) :: Γ) × Nat :=
  let field := state.nextField
  let spec : InitialField P L :=
    { ty := bindTy.base, owner := bindTy.owner, value := value }
  ({ initialFields := state.initialFields ++ [spec]
     wctx := WFCtx.cons hfresh state.wctx
     fieldOf := consFieldOf state field
     fieldOf_spec := by
       intro query queryTy h
       cases h with
       | here =>
           refine ⟨spec, ?_, rfl, rfl⟩
           simp [consFieldOf, field, nextField, spec]
       | there htail =>
           rcases state.fieldOf_spec htail with ⟨oldSpec, hget, hty, howner⟩
           refine ⟨oldSpec, ?_, hty, howner⟩
           change (state.initialFields ++ [spec])[state.fieldOf htail]? =
             some oldSpec
           rw [List.getElem?_append_left (state.fieldOf_lt htail)]
           exact hget },
   field)

end InitialState

/-- Body compiler accumulator. Initial fields are fixed; event nodes are
appended with output field id `initialFields.length + node`. -/
structure BuildState (P : Type) [DecidableEq P] (L : IExpr)
    (Γ : VCtx P L) where
  initialFields : List (InitialField P L)
  nodes : List (EventNode P L)
  wctx : WFCtx Γ
  fieldOf : {name : VarId} → {bindTy : BindTy P L} →
    VHasVar Γ name bindTy → Nat
  fieldOf_spec :
    ∀ {name : VarId} {bindTy : BindTy P L}
      (h : VHasVar Γ name bindTy),
        ∃ spec,
          ({ initialFields := initialFields, nodes := nodes } :
            Graph P L).field? (fieldOf h) = some spec ∧
          spec.ty = bindTy.base ∧ spec.owner = bindTy.owner
  fieldOf_available :
    ∀ {name : VarId} {bindTy : BindTy P L}
      (h : VHasVar Γ name bindTy),
        ({ initialFields := initialFields, nodes := nodes } :
          Graph P L).fieldAvailableBefore nodes.length (fieldOf h) = true
  graphWF :
    ({ initialFields := initialFields, nodes := nodes } : Graph P L).WF

namespace BuildState

variable {Γ : VCtx P L}

def fromInitial (state : InitialState P L Γ) : BuildState P L Γ where
  initialFields := state.initialFields
  nodes := []
  wctx := state.wctx
  fieldOf := state.fieldOf
  fieldOf_spec := by
    intro name bindTy h
    rcases state.fieldOf_spec h with ⟨spec, hget, hty, howner⟩
    refine
      ⟨{ ty := spec.ty, owner := spec.owner, source := .initial spec.value },
        ?_, hty, howner⟩
    unfold Graph.field?
    have hlt : state.fieldOf h < state.initialFields.length :=
      state.fieldOf_lt h
    simp only [dite_eq_ite, hlt, ↓reduceIte]
    simp only [hget]
  fieldOf_available := by
    intro name bindTy h
    rcases state.fieldOf_spec h with ⟨spec, hget, _hty, _howner⟩
    unfold Graph.fieldAvailableBefore Graph.field?
    have hlt : state.fieldOf h < state.initialFields.length :=
      state.fieldOf_lt h
    simp [hlt]
  graphWF := Graph.WF_empty state.initialFields

@[simp] theorem fromInitial_nodes (state : InitialState P L Γ) :
    (fromInitial state).nodes = [] :=
  rfl

@[simp] theorem fromInitial_initialFields (state : InitialState P L Γ) :
    (fromInitial state).initialFields = state.initialFields :=
  rfl

def nextNode (state : BuildState P L Γ) : Nat :=
  state.nodes.length

def nextField (state : BuildState P L Γ) : Nat :=
  state.initialFields.length + state.nextNode

theorem fieldOf_lt (state : BuildState P L Γ)
    {name : VarId} {bindTy : BindTy P L}
    (h : VHasVar Γ name bindTy) :
    state.fieldOf h < state.initialFields.length + state.nodes.length := by
  rcases state.fieldOf_spec h with ⟨_spec, hget, _hty, _howner⟩
  unfold Graph.field? at hget
  by_cases hlt : state.fieldOf h < state.initialFields.length
  · omega
  · simp only [dite_eq_ite, hlt, ↓reduceIte] at hget
    cases hnode :
        state.nodes[state.fieldOf h - state.initialFields.length]? with
    | none => simp [hnode] at hget
    | some event =>
        have hidx :
            state.fieldOf h - state.initialFields.length < state.nodes.length :=
          (List.getElem?_eq_some_iff.mp hnode).1
        omega

theorem fieldOf_eq_of_nodup (state : BuildState P L Γ)
    {name : VarId} {bindTy : BindTy P L}
    (h₁ h₂ : VHasVar Γ name bindTy) :
    state.fieldOf h₁ = state.fieldOf h₂ := by
  have hproof := HasVar.eq_of_nodup state.wctx h₁ h₂
  cases hproof
  rfl

def consFieldOf (state : BuildState P L Γ) (field : Nat)
    {name : VarId} {bindTy : BindTy P L} :
    {query : VarId} → {queryTy : BindTy P L} →
      VHasVar ((name, bindTy) :: Γ) query queryTy → Nat
  | _, _, .here => field
  | _, _, .there htail => state.fieldOf htail

/-- Append one event row and extend the compiler context with its output
field. -/
def addEvent (state : BuildState P L Γ)
    (name : VarId) (bindTy : BindTy P L) (sem : NodeSem P L)
    (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
          [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt
        state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem }) :
    BuildState P L ((name, bindTy) :: Γ) × Nat :=
  let field := state.nextField
  let event : EventNode P L :=
    { ty := bindTy.base, owner := bindTy.owner, sem := sem }
  ({ initialFields := state.initialFields
     nodes := state.nodes ++ [event]
     wctx := WFCtx.cons hfresh state.wctx
     fieldOf := consFieldOf state field
     fieldOf_spec := by
       intro query queryTy h
       cases h with
       | here =>
           refine
             ⟨{ ty := bindTy.base, owner := bindTy.owner,
                source := .event state.nextNode }, ?_, rfl, rfl⟩
           have hnot :
               ¬ state.initialFields.length + state.nodes.length <
                 state.initialFields.length := by omega
           simp [Graph.field?, consFieldOf, field, nextField, nextNode,
             event, hnot]
       | there htail =>
           rcases state.fieldOf_spec htail with ⟨oldSpec, hget, hty, howner⟩
           refine ⟨oldSpec, ?_, hty, howner⟩
           change
             ({ initialFields := state.initialFields,
                nodes := state.nodes ++ [event] } :
                Graph P L).field? (state.fieldOf htail) = some oldSpec
           exact Graph.field?_append_node_of_some
             state.initialFields state.nodes event hget
     fieldOf_available := by
       intro query queryTy h
       cases h with
       | here =>
           have hnot :
               ¬ state.initialFields.length + state.nodes.length <
                 state.initialFields.length := by omega
           simp [Graph.fieldAvailableBefore, Graph.field?, consFieldOf,
             field, nextField, nextNode, event, hnot]
       | there htail =>
           simp [consFieldOf, event]
           simpa [event] using
             Graph.fieldAvailableBefore_next_of_true
               state.initialFields state.nodes event
               (state.fieldOf_available htail)
     graphWF := by
       exact Graph.WF_append_event state.initialFields state.nodes event
         hnode state.graphWF },
   field)

@[simp] theorem addEvent_nodes (state : BuildState P L Γ)
    (name : VarId) (bindTy : BindTy P L) (sem : NodeSem P L)
    (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
          [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt
        state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem }) :
    (state.addEvent name bindTy sem hfresh hnode).1.nodes =
      state.nodes ++ [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] :=
  rfl

@[simp] theorem addEvent_initialFields (state : BuildState P L Γ)
    (name : VarId) (bindTy : BindTy P L) (sem : NodeSem P L)
    (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
          [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt
        state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem }) :
    (state.addEvent name bindTy sem hfresh hnode).1.initialFields =
      state.initialFields :=
  rfl

@[simp] theorem addEvent_fieldOf_here (state : BuildState P L Γ)
    (name : VarId) (bindTy : BindTy P L) (sem : NodeSem P L)
    (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
          [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt
        state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem }) :
    (state.addEvent name bindTy sem hfresh hnode).1.fieldOf
      (VHasVar.here (x := name) (τ := bindTy)) =
        state.nextField :=
  rfl

@[simp] theorem addEvent_fieldOf_there (state : BuildState P L Γ)
    (name : VarId) (bindTy : BindTy P L) (sem : NodeSem P L)
    (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
          [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt
        state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem })
    {query : VarId} {queryTy : BindTy P L}
    (h : VHasVar Γ query queryTy) :
    (state.addEvent name bindTy sem hfresh hnode).1.fieldOf
      (VHasVar.there h) =
        state.fieldOf h :=
  rfl

/-- Field id for a variable in the public erased context. -/
def fieldOfPub (state : BuildState P L Γ)
    {name : VarId} {ty : L.Ty}
    (hvar : HasVar (erasePubVCtx Γ) name ty) : Nat :=
  state.fieldOf (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar))

/-- Typed graph field reference for a variable in the public erased context. -/
def fieldRefOfPub (state : BuildState P L Γ)
    {name : VarId} {ty : L.Ty}
    (hvar : HasVar (erasePubVCtx Γ) name ty) : FieldRef L :=
  { field := state.fieldOfPub hvar, ty := ty }

/-- Typed graph field reference for a variable in a player's visible context. -/
def fieldRefOfView (state : BuildState P L Γ) (who : P)
    {name : VarId} {bindTy : BindTy P L}
    (hvar : VHasVar (viewVCtx who Γ) name bindTy) : FieldRef L :=
  { field := state.fieldOf (VHasVar.ofViewVCtx hvar), ty := bindTy.base }

/-- Typed graph field reference for a name known to occur in the public erased
context. -/
private noncomputable def fieldRefOfPubName (state : BuildState P L Γ)
    (name : VarId)
    (hmem : name ∈ (erasePubVCtx Γ).map Prod.fst) : FieldRef L :=
  let hvar := hasVarOfNameMem (L := L)
    (WFCtx.erasePubVCtx state.wctx) hmem
  { field := state.fieldOfPub hvar.2, ty := hvar.1 }

end BuildState

/-- Public graph field references read by an expression. -/
noncomputable def exprReadRefs
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (expr : L.Expr (erasePubVCtx Γ) ty) : Finset (FieldRef L) :=
  (L.exprDeps expr).attach.image fun dep =>
    state.fieldRefOfPubName dep.1 (L.expr_deps_context expr dep.1 dep.2)

/-- Public graph field references read by a distribution. -/
noncomputable def distReadRefs
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty) : Finset (FieldRef L) :=
  (L.distDeps dist).attach.image fun dep =>
    state.fieldRefOfPubName dep.1 (L.dist_deps_context dist dep.1 dep.2)

/-- Structurally enumerate graph references for every binding in a context. -/
def fieldRefsOfCtx
    {Γ : VCtx P L}
    (fieldOf :
      {name : VarId} → {bindTy : BindTy P L} →
        VHasVar Γ name bindTy → Nat) :
    Finset (FieldRef L) :=
  match Γ with
  | [] => ∅
  | (_name, bindTy) :: tail =>
      let rest :=
        fieldRefsOfCtx (Γ := tail)
          (fun {_name} {_bindTy} h => fieldOf (VHasVar.there h))
      insert { field := fieldOf VHasVar.here, ty := bindTy.base } rest

omit [DecidableEq P] in
@[simp] theorem fieldRefsOfCtx_nil
    (fieldOf :
      {name : VarId} → {bindTy : BindTy P L} →
        VHasVar ([] : VCtx P L) name bindTy → Nat) :
    fieldRefsOfCtx fieldOf = ∅ := rfl

omit [DecidableEq P] in
@[simp] theorem fieldRefsOfCtx_cons
    {Γ : VCtx P L} {name : VarId} {bindTy : BindTy P L}
    (fieldOf :
      {query : VarId} → {queryTy : BindTy P L} →
        VHasVar ((name, bindTy) :: Γ) query queryTy → Nat) :
    fieldRefsOfCtx fieldOf =
      insert { field := fieldOf VHasVar.here, ty := bindTy.base }
        (fieldRefsOfCtx
          (fun {_name} {_bindTy} h => fieldOf (VHasVar.there h))) := rfl

/-- Graph field references visible to a player in the current source context. -/
def visibleFieldRefs
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (who : P) : Finset (FieldRef L) :=
  fieldRefsOfCtx (Γ := viewVCtx who Γ)
    (fun {_name} {_bindTy} h =>
      state.fieldOf (VHasVar.ofViewVCtx h))

omit [DecidableEq P] in
theorem fieldRefsOfCtx_available
    {Γ : VCtx P L}
    (fieldOf :
      {name : VarId} → {bindTy : BindTy P L} →
        VHasVar Γ name bindTy → Nat)
    (availableAt : Nat → Bool)
    (havailable :
      ∀ {name : VarId} {bindTy : BindTy P L}
        (h : VHasVar Γ name bindTy), availableAt (fieldOf h) = true)
    :
    ∀ ref, ref ∈ fieldRefsOfCtx fieldOf →
      availableAt ref.field = true := by
  induction Γ with
  | nil =>
      intro ref href
      simp [fieldRefsOfCtx] at href
  | cons head tail ih =>
      obtain ⟨_headName, _headTy⟩ := head
      intro ref href
      have hmem :
          ref = { field := fieldOf VHasVar.here, ty := _headTy.base } ∨
            ref ∈
              fieldRefsOfCtx
                (fun {_name} {_bindTy} h =>
                  fieldOf (VHasVar.there h)) := by
        simpa [fieldRefsOfCtx] using href
      rcases hmem with hhead | htail
      · subst ref
        exact havailable VHasVar.here
      · exact
          ih
            (fieldOf := fun {_name} {_bindTy} h =>
              fieldOf (VHasVar.there h))
            (by
              intro name bindTy h
              exact havailable (VHasVar.there h))
            ref htail

omit [DecidableEq P] in
theorem fieldRefsOfCtx_store_available
    {Γ : VCtx P L}
    (fieldOf :
      {name : VarId} → {bindTy : BindTy P L} →
        VHasVar Γ name bindTy → Nat)
    (store : Store L)
    (available :
      ∀ {name : VarId} {bindTy : BindTy P L}
        (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (fieldOf h) bindTy.base = some value)
    :
    ∀ ref, ref ∈ fieldRefsOfCtx fieldOf →
      ∃ value, Store.getAs store ref.field ref.ty = some value := by
  induction Γ with
  | nil =>
      intro ref href
      simp [fieldRefsOfCtx] at href
  | cons head tail ih =>
      obtain ⟨_headName, _headTy⟩ := head
      intro ref href
      have hmem :
          ref = { field := fieldOf VHasVar.here, ty := _headTy.base } ∨
            ref ∈
              fieldRefsOfCtx
                (fun {_name} {_bindTy} h =>
                  fieldOf (VHasVar.there h)) := by
        simpa [fieldRefsOfCtx] using href
      rcases hmem with hhead | htail
      · subst ref
        exact available VHasVar.here
      · exact
          ih
            (fieldOf := fun {_name} {_bindTy} h =>
              fieldOf (VHasVar.there h))
            (by
              intro name bindTy h
              exact available (VHasVar.there h))
            ref htail

theorem fieldRefsOfCtx_visible
    {Γ : VCtx P L}
    (fieldOf :
      {name : VarId} → {bindTy : BindTy P L} →
        VHasVar Γ name bindTy → Nat)
    (graph : Graph P L)
    (who : P)
    (hspec :
      ∀ {name : VarId} {bindTy : BindTy P L}
        (h : VHasVar Γ name bindTy),
        ∃ spec, graph.field? (fieldOf h) = some spec ∧
          spec.ty = bindTy.base ∧ spec.owner = bindTy.owner)
    (visible :
      ∀ {name : VarId} {bindTy : BindTy P L}
        (_h : VHasVar Γ name bindTy),
        bindTy.owner = none ∨ bindTy.owner = some who)
    :
    ∀ ref, ref ∈ fieldRefsOfCtx fieldOf →
      graph.fieldRefVisibleTo who ref := by
  induction Γ with
  | nil =>
      intro ref href
      simp [fieldRefsOfCtx] at href
  | cons head tail ih =>
      obtain ⟨_headName, _headTy⟩ := head
      intro ref href
      have hmem :
          ref = { field := fieldOf VHasVar.here, ty := _headTy.base } ∨
            ref ∈
              fieldRefsOfCtx
                (fun {_name} {_bindTy} h =>
                  fieldOf (VHasVar.there h)) := by
        simpa [fieldRefsOfCtx] using href
      rcases hmem with hhead | htail
      · subst ref
        rcases hspec VHasVar.here with ⟨spec, hfield, hty, howner⟩
        exact
          ⟨spec, hfield, hty,
            by
              rw [howner]
              exact visible VHasVar.here⟩
      · exact ih
          (fieldOf := fun {_name} {_bindTy} h =>
            fieldOf (VHasVar.there h))
          (by
            intro name bindTy h
            exact hspec (VHasVar.there h))
          (by
            intro name bindTy h
            exact visible (VHasVar.there h))
          ref htail

omit [DecidableEq P] in
theorem fieldRefOfCtx_mem
    {Γ : VCtx P L}
    (fieldOf :
      {name : VarId} → {bindTy : BindTy P L} →
        VHasVar Γ name bindTy → Nat)
    {name : VarId} {bindTy : BindTy P L}
    (hvar : VHasVar Γ name bindTy) :
    ({ field := fieldOf hvar,
       ty := bindTy.base } : FieldRef L) ∈
      fieldRefsOfCtx fieldOf := by
  induction hvar with
  | here =>
      simp [fieldRefsOfCtx]
  | there htail ih =>
      simp [fieldRefsOfCtx, ih]

theorem fieldRefOfView_mem_visibleFieldRefs
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (who : P)
    {name : VarId} {bindTy : BindTy P L}
    (hvar : VHasVar (viewVCtx who Γ) name bindTy) :
    state.fieldRefOfView who hvar ∈ visibleFieldRefs state who := by
  simpa [visibleFieldRefs, BuildState.fieldRefOfView]
    using
      fieldRefOfCtx_mem
        (fieldOf := fun {_name} {_bindTy} h =>
          state.fieldOf (VHasVar.ofViewVCtx h))
        hvar

/-- Any dependency witness of an expression maps to a typed read reference in
the expression footprint. -/
theorem exprReadRefs_mem
    {Γ : VCtx P L} {ty depTy : L.Ty} {name : VarId}
    (state : BuildState P L Γ)
    (expr : L.Expr (erasePubVCtx Γ) ty)
    (hvar : HasVar (erasePubVCtx Γ) name depTy)
    (hmem : name ∈ L.exprDeps expr) :
    state.fieldRefOfPub hvar ∈ exprReadRefs state expr := by
  classical
  unfold exprReadRefs BuildState.fieldRefOfPubName BuildState.fieldRefOfPub
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨name, hmem⟩, by simp, ?_⟩
  let chosen :=
    hasVarOfNameMem (L := L) (WFCtx.erasePubVCtx state.wctx)
      (L.expr_deps_context expr name hmem)
  have hty : chosen.1 = depTy :=
    HasVar.type_unique (WFCtx.erasePubVCtx state.wctx) chosen.2 hvar
  cases hty
  have hproof : chosen.2 = hvar :=
    HasVar.eq_of_nodup (WFCtx.erasePubVCtx state.wctx) chosen.2 hvar
  cases hproof
  rfl

theorem exprReadRefs_store_available
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value)
    {ty : L.Ty} (expr : L.Expr (erasePubVCtx Γ) ty) :
    ∀ ref, ref ∈ exprReadRefs state expr →
      ∃ value, Store.getAs store ref.field ref.ty = some value := by
  intro ref href
  unfold exprReadRefs at href
  rcases Finset.mem_image.mp href with ⟨dep, _hdep, hrefEq⟩
  subst ref
  simpa [BuildState.fieldRefOfPubName, BuildState.fieldOfPub] using
    available
      (VHasVar.ofPubVCtx (HasVar.toVHasVarPub
        (hasVarOfNameMem (L := L)
          (WFCtx.erasePubVCtx state.wctx)
          (L.expr_deps_context expr dep.1 dep.2)).2))

/-- Any dependency witness of a distribution maps to a typed read reference in
the distribution footprint. -/
theorem distReadRefs_mem
    {Γ : VCtx P L} {ty depTy : L.Ty} {name : VarId}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (hvar : HasVar (erasePubVCtx Γ) name depTy)
    (hmem : name ∈ L.distDeps dist) :
    state.fieldRefOfPub hvar ∈ distReadRefs state dist := by
  classical
  unfold distReadRefs BuildState.fieldRefOfPubName BuildState.fieldRefOfPub
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨name, hmem⟩, by simp, ?_⟩
  let chosen :=
    hasVarOfNameMem (L := L) (WFCtx.erasePubVCtx state.wctx)
      (L.dist_deps_context dist name hmem)
  have hty : chosen.1 = depTy :=
    HasVar.type_unique (WFCtx.erasePubVCtx state.wctx) chosen.2 hvar
  cases hty
  have hproof : chosen.2 = hvar :=
    HasVar.eq_of_nodup (WFCtx.erasePubVCtx state.wctx) chosen.2 hvar
  cases hproof
  rfl

theorem distReadRefs_store_available
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value)
    {ty : L.Ty} (dist : L.DistExpr (erasePubVCtx Γ) ty) :
    ∀ ref, ref ∈ distReadRefs state dist →
      ∃ value, Store.getAs store ref.field ref.ty = some value := by
  intro ref href
  unfold distReadRefs at href
  rcases Finset.mem_image.mp href with ⟨dep, _hdep, hrefEq⟩
  subst ref
  simpa [BuildState.fieldRefOfPubName, BuildState.fieldOfPub] using
    available
      (VHasVar.ofPubVCtx (HasVar.toVHasVarPub
        (hasVarOfNameMem (L := L)
          (WFCtx.erasePubVCtx state.wctx)
          (L.dist_deps_context dist dep.1 dep.2)).2))

theorem exprReadRefs_available
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (expr : L.Expr (erasePubVCtx Γ) ty) :
    ∀ ref, ref ∈ exprReadRefs state expr →
      ({ initialFields := state.initialFields, nodes := state.nodes } :
        Graph P L).fieldAvailableBefore state.nodes.length ref.field = true := by
  intro ref href
  rcases Finset.mem_image.mp href with ⟨dep, _hdep, rfl⟩
  unfold BuildState.fieldRefOfPubName BuildState.fieldOfPub
  exact state.fieldOf_available
    (VHasVar.ofPubVCtx (HasVar.toVHasVarPub
      (hasVarOfNameMem (L := L)
        (WFCtx.erasePubVCtx state.wctx)
        (L.expr_deps_context expr dep.1 dep.2)).2))

theorem exprReadRefs_public
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (expr : L.Expr (erasePubVCtx Γ) ty) :
    ∀ ref, ref ∈ exprReadRefs state expr →
      ({ initialFields := state.initialFields, nodes := state.nodes } :
        Graph P L).fieldRefPublic ref := by
  intro ref href
  rcases Finset.mem_image.mp href with ⟨dep, _hdep, rfl⟩
  unfold BuildState.fieldRefOfPubName BuildState.fieldOfPub
  let hvar :=
    VHasVar.ofPubVCtx (HasVar.toVHasVarPub
      (hasVarOfNameMem (L := L)
        (WFCtx.erasePubVCtx state.wctx)
        (L.expr_deps_context expr dep.1 dep.2)).2)
  rcases state.fieldOf_spec hvar with ⟨spec, hget, _hty, howner⟩
  exact ⟨spec, hget, _hty, howner⟩

theorem distReadRefs_available
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty) :
    ∀ ref, ref ∈ distReadRefs state dist →
      ({ initialFields := state.initialFields, nodes := state.nodes } :
        Graph P L).fieldAvailableBefore state.nodes.length ref.field = true := by
  intro ref href
  rcases Finset.mem_image.mp href with ⟨dep, _hdep, rfl⟩
  unfold BuildState.fieldRefOfPubName BuildState.fieldOfPub
  exact state.fieldOf_available
    (VHasVar.ofPubVCtx (HasVar.toVHasVarPub
      (hasVarOfNameMem (L := L)
        (WFCtx.erasePubVCtx state.wctx)
        (L.dist_deps_context dist dep.1 dep.2)).2))

theorem distReadRefs_public
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty) :
    ∀ ref, ref ∈ distReadRefs state dist →
      ({ initialFields := state.initialFields, nodes := state.nodes } :
        Graph P L).fieldRefPublic ref := by
  intro ref href
  rcases Finset.mem_image.mp href with ⟨dep, _hdep, rfl⟩
  unfold BuildState.fieldRefOfPubName BuildState.fieldOfPub
  let hvar :=
    VHasVar.ofPubVCtx (HasVar.toVHasVarPub
      (hasVarOfNameMem (L := L)
        (WFCtx.erasePubVCtx state.wctx)
        (L.dist_deps_context dist dep.1 dep.2)).2)
  rcases state.fieldOf_spec hvar with ⟨spec, hget, _hty, howner⟩
  exact ⟨spec, hget, _hty, howner⟩

theorem visibleFieldRefs_available
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (who : P) :
    ∀ ref, ref ∈ visibleFieldRefs state who →
      ({ initialFields := state.initialFields, nodes := state.nodes } :
        Graph P L).fieldAvailableBefore state.nodes.length ref.field = true := by
  simpa [visibleFieldRefs] using
    fieldRefsOfCtx_available
      (fieldOf := fun {_name} {_bindTy} h =>
        state.fieldOf (VHasVar.ofViewVCtx h))
      (availableAt := fun field =>
        ({ initialFields := state.initialFields, nodes := state.nodes } :
          Graph P L).fieldAvailableBefore state.nodes.length field)
      (by
        intro name bindTy h
        exact state.fieldOf_available (VHasVar.ofViewVCtx h))

theorem visibleFieldRefs_store_available
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (who : P) (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value) :
    ∀ ref, ref ∈ visibleFieldRefs state who →
      ∃ value, Store.getAs store ref.field ref.ty = some value := by
  simpa [visibleFieldRefs] using
    fieldRefsOfCtx_store_available
      (fieldOf := fun {_name} {_bindTy} h =>
        state.fieldOf (VHasVar.ofViewVCtx h))
      store
      (by
        intro name bindTy h
        exact available (VHasVar.ofViewVCtx h))

theorem visibleFieldRefs_visible
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (who : P) :
    ∀ ref, ref ∈ visibleFieldRefs state who →
      ({ initialFields := state.initialFields, nodes := state.nodes } :
        Graph P L).fieldRefVisibleTo who ref := by
  simpa [visibleFieldRefs] using
    fieldRefsOfCtx_visible
      (fieldOf := fun {_name} {_bindTy} h =>
        state.fieldOf (VHasVar.ofViewVCtx h))
      (graph :=
        ({ initialFields := state.initialFields, nodes := state.nodes } :
          Graph P L))
      who
      (by
        intro name bindTy h
        exact state.fieldOf_spec (VHasVar.ofViewVCtx h))
      (by
        intro name bindTy h
        exact viewVCtx_owner h)

/-- Read a source variable through its proof-indexed graph field. -/
noncomputable def sourceValuePub
    {Γ : VCtx P L} {reads : Finset (FieldRef L)}
    (state : BuildState P L Γ) (env : ReadEnv L reads)
    {name : VarId} {ty : L.Ty}
    (hvar : HasVar (erasePubVCtx Γ) name ty)
    (href : state.fieldRefOfPub hvar ∈ reads) :
    L.Val ty :=
  env.read (state.fieldRefOfPub hvar) href

/-- Reconstruct a source environment from a graph store and proof that every
source binding has a value at its compiled graph field. -/
noncomputable def sourceEnvOfStore
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value) :
    VEnv L Γ :=
  fun _name _bindTy h => Classical.choose (available h)

theorem sourceEnvOfStore_get
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value)
    {name bindTy} (h : VHasVar Γ name bindTy) :
    Store.getAs store (state.fieldOf h) bindTy.base =
      some ((sourceEnvOfStore state store available).get h) :=
  Classical.choose_spec (available h)

theorem sourceEnvOfStore_irrel
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (store : Store L)
    (available available' :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value) :
    sourceEnvOfStore state store available =
      sourceEnvOfStore state store available' := by
  funext name bindTy h
  have hleft := sourceEnvOfStore_get state store available h
  have hright := sourceEnvOfStore_get state store available' h
  exact Option.some.inj (hleft.symm.trans hright)

/-- Read a visible source variable through its proof-indexed graph field. -/
noncomputable def sourceValueView
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (who : P)
    (env : ReadEnv L (visibleFieldRefs state who))
    {name : VarId} {ty : L.Ty}
    (hvar : HasVar (eraseVCtx (viewVCtx who Γ)) name ty) :
    L.Val ty := by
  classical
  let lifted := HasVar.toVHasVar (Player := P) (L := L) hvar
  let ref := state.fieldRefOfView who lifted.2.1
  have href : ref ∈ visibleFieldRefs state who := by
    exact fieldRefOfView_mem_visibleFieldRefs state who lifted.2.1
  have hty : ref.ty = ty := by
    unfold ref BuildState.fieldRefOfView
    exact lifted.2.2.down
  exact cast (congrArg L.Val hty) (env.read ref href)

/-- Reconstruct the actor-visible erased source environment from the graph
choice environment of a compiled commit guard. -/
noncomputable def viewEnvOfReadEnv
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (who : P)
    (env : ReadEnv L (visibleFieldRefs state who)) :
    Env L.Val (eraseVCtx (viewVCtx who Γ)) :=
  fun _name _ty hvar => sourceValueView state who env hvar

/-- Compile a terminal payoff expression into an integer graph projection. -/
noncomputable def eventPayoffOf
    {Γ : VCtx P L}
    (state : BuildState P L Γ)
    (expr : L.Expr (erasePubVCtx Γ) L.int) : EventPayoff L :=
  {
    reads := exprReadRefs state expr
    eval := fun env =>
      L.toInt (L.evalDeps expr fun _name _depTy hvar hmem =>
        sourceValuePub state env hvar
          (exprReadRefs_mem state expr hvar hmem)) }

/-- A compiled payoff projection agrees with its source payoff expression
whenever the graph read environment agrees with the source public environment
on the expression's declared dependencies. -/
theorem eventPayoffOf_eval_eq_eval
    {Γ : VCtx P L}
    (state : BuildState P L Γ)
    (expr : L.Expr (erasePubVCtx Γ) L.int)
    (sourceEnv : Env L.Val (erasePubVCtx Γ))
    (readEnv : EventGraph.ReadEnv L (eventPayoffOf state expr).reads)
    (hagrees :
      ∀ {name ty} (hvar : HasVar (erasePubVCtx Γ) name ty)
        (hmem : name ∈ L.exprDeps expr),
        sourceValuePub state readEnv hvar
          (exprReadRefs_mem state expr hvar hmem) =
          sourceEnv name ty hvar) :
    (eventPayoffOf state expr).eval readEnv =
      L.toInt (L.eval expr sourceEnv) := by
  change
    L.toInt
      (L.evalDeps expr fun _name _depTy hvar hmem =>
        sourceValuePub state readEnv hvar
          (exprReadRefs_mem state expr hvar hmem)) =
      L.toInt (L.eval expr sourceEnv)
  rw [← L.evalDeps_eq_eval expr sourceEnv]
  congr
  funext name ty hvar hmem
  exact hagrees hvar hmem

theorem eventPayoffOf_readEnv_agrees_sourceEnvOfStore
    {Γ : VCtx P L}
    (state : BuildState P L Γ)
    (expr : L.Expr (erasePubVCtx Γ) L.int)
    (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value) :
    ∃ readEnv,
      ReadEnv.ofStore? store (eventPayoffOf state expr).reads =
        some readEnv ∧
      ∀ {name ty} (hvar : HasVar (erasePubVCtx Γ) name ty)
        (hmem : name ∈ L.exprDeps expr),
        sourceValuePub state readEnv hvar
          (exprReadRefs_mem state expr hvar hmem) =
          VEnv.erasePubEnv (sourceEnvOfStore state store available)
            name ty hvar := by
  let readAvailable :
      ∀ ref, ref ∈ (eventPayoffOf state expr).reads →
        ∃ value, Store.getAs store ref.field ref.ty = some value := by
    simpa [eventPayoffOf] using
      exprReadRefs_store_available state store available expr
  let readEnv := ReadEnv.ofStore store
    (eventPayoffOf state expr).reads readAvailable
  have hreadEnv :
      ReadEnv.ofStore? store (eventPayoffOf state expr).reads =
        some readEnv := by
    unfold ReadEnv.ofStore?
    rw [dif_pos readAvailable]
  refine ⟨readEnv, hreadEnv, ?_⟩
  intro name ty hvar hmem
  have hreadStore :
      Store.getAs store (state.fieldRefOfPub hvar).field
          (state.fieldRefOfPub hvar).ty =
        some (readEnv.read (state.fieldRefOfPub hvar)
          (exprReadRefs_mem state expr hvar hmem)) :=
    ReadEnv.ofStore?_read hreadEnv
      (exprReadRefs_mem state expr hvar hmem)
  have hsourceStore :
      Store.getAs store
          (state.fieldOf
            (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar)))
          ty =
        some ((sourceEnvOfStore state store available).get
          (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar))) := by
    simpa [BuildState.fieldRefOfPub, BuildState.fieldOfPub] using
      sourceEnvOfStore_get state store available
        (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar))
  have hvalue :
      sourceValuePub state readEnv hvar
          (exprReadRefs_mem state expr hvar hmem) =
        (sourceEnvOfStore state store available).get
          (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar)) := by
    have hreadStore' :
        Store.getAs store
            (state.fieldOf
              (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar)))
            ty =
          some (sourceValuePub state readEnv hvar
            (exprReadRefs_mem state expr hvar hmem)) := by
      simpa [sourceValuePub, BuildState.fieldRefOfPub,
        BuildState.fieldOfPub] using hreadStore
    exact Option.some.inj (hreadStore'.symm.trans hsourceStore)
  simpa [sourceValuePub, VEnv.erasePubEnv_get, VEnv.get] using hvalue

/-- Compile a source distribution into an executable graph-local PMF. -/
noncomputable def eventDistOf
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1) :
    EventDist L :=
  {
    ty := ty
    reads := distReadRefs state dist
    eval := fun env =>
      let depEnv :
          (name : VarId) → (depTy : L.Ty) →
            HasVar (erasePubVCtx Γ) name depTy →
              name ∈ L.distDeps dist → L.Val depTy :=
        fun _name _depTy hvar hmem =>
          sourceValuePub state env hvar
            (distReadRefs_mem state dist hvar hmem)
      (L.evalDistDeps dist depEnv).toPMF (normalized depEnv) }

/-- A compiled distribution evaluates to the same normalized finite
distribution as the source distribution when its graph read environment agrees
with the source public environment on the distribution dependencies. -/
theorem eventDistOf_eval_eq_eval
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1)
    (sourceEnv : Env L.Val (erasePubVCtx Γ))
    (readEnv : EventGraph.ReadEnv L (eventDistOf state dist normalized).reads)
    (hagrees :
      ∀ {name depTy} (hvar : HasVar (erasePubVCtx Γ) name depTy)
        (hmem : name ∈ L.distDeps dist),
        sourceValuePub state readEnv hvar
          (distReadRefs_mem state dist hvar hmem) =
          sourceEnv name depTy hvar) :
    ∃ hnormalized : FWeight.totalWeight (L.evalDist dist sourceEnv) = 1,
      (eventDistOf state dist normalized).eval readEnv =
        (L.evalDist dist sourceEnv).toPMF hnormalized := by
  let depEnv :
      (name : VarId) → (depTy : L.Ty) →
        HasVar (erasePubVCtx Γ) name depTy →
          name ∈ L.distDeps dist → L.Val depTy :=
    fun _name _depTy hvar hmem =>
      sourceValuePub state readEnv hvar
        (distReadRefs_mem state dist hvar hmem)
  have hdist :
      L.evalDistDeps dist depEnv = L.evalDist dist sourceEnv := by
    rw [← L.evalDistDeps_eq_evalDist dist sourceEnv]
    congr
    funext name depTy hvar hmem
    exact hagrees hvar hmem
  let hnormalized :
      FWeight.totalWeight (L.evalDist dist sourceEnv) = 1 := by
    rw [← hdist]
    exact normalized depEnv
  refine ⟨hnormalized, ?_⟩
  change
    (L.evalDistDeps dist depEnv).toPMF (normalized depEnv) =
      (L.evalDist dist sourceEnv).toPMF hnormalized
  apply PMF.ext
  intro value
  rw [FWeight.toPMF_apply, FWeight.toPMF_apply, hdist]

theorem eventDistOf_readEnv_agrees_sourceEnvOfStore_of_readEnv
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1)
    (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value)
    (readEnv : ReadEnv L (eventDistOf state dist normalized).reads)
    (hreadEnv :
      ReadEnv.ofStore? store (eventDistOf state dist normalized).reads =
        some readEnv) :
    ∀ {name depTy} (hvar : HasVar (erasePubVCtx Γ) name depTy)
      (hmem : name ∈ L.distDeps dist),
      sourceValuePub state readEnv hvar
        (distReadRefs_mem state dist hvar hmem) =
        VEnv.erasePubEnv (sourceEnvOfStore state store available)
          name depTy hvar := by
  intro name depTy hvar hmem
  have hreadStore :
      Store.getAs store (state.fieldRefOfPub hvar).field
          (state.fieldRefOfPub hvar).ty =
        some (readEnv.read (state.fieldRefOfPub hvar)
          (distReadRefs_mem state dist hvar hmem)) :=
    ReadEnv.ofStore?_read hreadEnv
      (distReadRefs_mem state dist hvar hmem)
  have hsourceStore :
      Store.getAs store
          (state.fieldOf
            (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar)))
          depTy =
        some ((sourceEnvOfStore state store available).get
          (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar))) := by
    simpa [BuildState.fieldRefOfPub, BuildState.fieldOfPub] using
      sourceEnvOfStore_get state store available
        (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar))
  have hvalue :
      sourceValuePub state readEnv hvar
          (distReadRefs_mem state dist hvar hmem) =
        (sourceEnvOfStore state store available).get
          (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar)) := by
    have hreadStore' :
        Store.getAs store
            (state.fieldOf
              (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hvar)))
            depTy =
          some (sourceValuePub state readEnv hvar
            (distReadRefs_mem state dist hvar hmem)) := by
      simpa [sourceValuePub, BuildState.fieldRefOfPub,
        BuildState.fieldOfPub] using hreadStore
    exact Option.some.inj (hreadStore'.symm.trans hsourceStore)
  simpa [sourceValuePub, VEnv.erasePubEnv_get, VEnv.get] using hvalue

theorem eventDistOf_readEnv_agrees_sourceEnvOfStore
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1)
    (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value) :
    ∃ readEnv,
      ReadEnv.ofStore? store (eventDistOf state dist normalized).reads =
        some readEnv ∧
      ∀ {name depTy} (hvar : HasVar (erasePubVCtx Γ) name depTy)
        (hmem : name ∈ L.distDeps dist),
        sourceValuePub state readEnv hvar
          (distReadRefs_mem state dist hvar hmem) =
          VEnv.erasePubEnv (sourceEnvOfStore state store available)
            name depTy hvar := by
  let readAvailable :
      ∀ ref, ref ∈ (eventDistOf state dist normalized).reads →
        ∃ value, Store.getAs store ref.field ref.ty = some value := by
    simpa [eventDistOf] using
      distReadRefs_store_available state store available dist
  let readEnv := ReadEnv.ofStore store
    (eventDistOf state dist normalized).reads readAvailable
  have hreadEnv :
      ReadEnv.ofStore? store (eventDistOf state dist normalized).reads =
        some readEnv := by
    unfold ReadEnv.ofStore?
    rw [dif_pos readAvailable]
  refine ⟨readEnv, hreadEnv, ?_⟩
  exact
    eventDistOf_readEnv_agrees_sourceEnvOfStore_of_readEnv
      state dist normalized store available readEnv hreadEnv

/-- Compile a source commit guard. `choiceReads` is the actor's whole visible
source context: the information footprint for choosing this commit, not an
exact syntactic dependency set for evaluating the guard expression. -/
noncomputable def eventGuardOf
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool) : EventGuard L :=
  {
    ty := actionTy
    choiceReads := visibleFieldRefs state who
    eval := fun action env =>
      evalGuard (Player := P) (L := L) guard action
        (viewEnvOfReadEnv state who env) }

theorem eventGuardOf_eval_eq_eval
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool)
    (action : L.Val actionTy)
    (readEnv : ReadEnv L (eventGuardOf state who guard).choiceReads) :
    (eventGuardOf state who guard).eval action readEnv =
      evalGuard (Player := P) (L := L) guard action
        (viewEnvOfReadEnv state who readEnv) := rfl

theorem eventGuardOf_readEnv_of_sourceStoreAvailable
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool)
    (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value) :
    ∃ readEnv,
      ReadEnv.ofStore? store (eventGuardOf state who guard).choiceReads =
        some readEnv := by
  let readAvailable :
      ∀ ref, ref ∈ (eventGuardOf state who guard).choiceReads →
        ∃ value, Store.getAs store ref.field ref.ty = some value := by
    simpa [eventGuardOf] using
      visibleFieldRefs_store_available state who store available
  let readEnv := ReadEnv.ofStore store
    (eventGuardOf state who guard).choiceReads readAvailable
  refine ⟨readEnv, ?_⟩
  unfold ReadEnv.ofStore?
  rw [dif_pos readAvailable]

theorem viewEnvOfReadEnv_eq_eraseEnv_sourceEnvOfStore
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (who : P)
    (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value)
    (readEnv : ReadEnv L (visibleFieldRefs state who))
    (hreadEnv :
      ReadEnv.ofStore? store (visibleFieldRefs state who) =
        some readEnv) :
    viewEnvOfReadEnv state who readEnv =
      VEnv.eraseEnv (VEnv.toView who
        (sourceEnvOfStore state store available)) := by
  funext name ty hvar
  unfold viewEnvOfReadEnv sourceValueView
  let lifted := HasVar.toVHasVar (Player := P) (L := L) hvar
  let ref := state.fieldRefOfView who lifted.2.1
  have href : ref ∈ visibleFieldRefs state who := by
    exact fieldRefOfView_mem_visibleFieldRefs state who lifted.2.1
  have hreadStore :
      Store.getAs store ref.field ref.ty =
        some (readEnv.read ref href) :=
    ReadEnv.ofStore?_read hreadEnv href
  have hsourceStore :
      Store.getAs store
          (state.fieldOf (VHasVar.ofViewVCtx lifted.2.1))
          lifted.1.base =
        some ((sourceEnvOfStore state store available).get
          (VHasVar.ofViewVCtx lifted.2.1)) := by
    simpa using
      sourceEnvOfStore_get state store available
        (VHasVar.ofViewVCtx lifted.2.1)
  have hreadStore' :
      Store.getAs store
          (state.fieldOf (VHasVar.ofViewVCtx lifted.2.1))
          lifted.1.base =
        some (readEnv.read ref href) := by
    simpa [ref, BuildState.fieldRefOfView] using hreadStore
  have hvalueBase :
      readEnv.read ref href =
        (sourceEnvOfStore state store available).get
          (VHasVar.ofViewVCtx lifted.2.1) :=
    Option.some.inj (hreadStore'.symm.trans hsourceStore)
  have hviewErased :
      VEnv.eraseEnv
          (VEnv.toView who (sourceEnvOfStore state store available))
          name lifted.1.base lifted.2.1.toErased =
        (sourceEnvOfStore state store available).get
          (VHasVar.ofViewVCtx lifted.2.1) := by
    have h :=
      VEnv.eraseEnv_get_of_erased
        (VEnv.toView who (sourceEnvOfStore state store available))
        lifted.2.1
    exact h
  have herasedHEq :
      HEq
        (VEnv.eraseEnv
          (VEnv.toView who (sourceEnvOfStore state store available))
          name lifted.1.base lifted.2.1.toErased)
        (VEnv.eraseEnv
          (VEnv.toView who (sourceEnvOfStore state store available))
          name ty hvar) :=
    VEnv.eraseEnv_toErased_eq
      (VEnv.toView who (sourceEnvOfStore state store available)) hvar
  have htarget :
      HEq
        (readEnv.read ref href)
        (VEnv.eraseEnv
          (VEnv.toView who (sourceEnvOfStore state store available))
          name ty hvar) := by
    have hreadLifted :
        HEq
          (readEnv.read ref href)
          (VEnv.eraseEnv
            (VEnv.toView who (sourceEnvOfStore state store available))
            name lifted.1.base lifted.2.1.toErased) := by
      rw [hvalueBase, hviewErased]
      exact HEq.rfl
    exact HEq.trans hreadLifted herasedHEq
  have hcast :
      HEq
        (cast (congrArg L.Val (by
          unfold ref BuildState.fieldRefOfView
          exact lifted.2.2.down))
            (readEnv.read ref href))
        (readEnv.read ref href) :=
    cast_heq _ _
  exact eq_of_heq (HEq.trans hcast htarget)

theorem eventGuardOf_live_of_legal
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool)
    (legal :
      ∀ env : Env L.Val (eraseVCtx (viewVCtx who Γ)),
        ∃ value : L.Val actionTy,
          evalGuard (Player := P) (L := L) guard value env = true) :
    ∀ env : ReadEnv L (eventGuardOf state who guard).choiceReads,
      ∃ value : L.Val (eventGuardOf state who guard).ty,
        (eventGuardOf state who guard).eval value env = true := by
  intro env
  exact legal (viewEnvOfReadEnv state who env)

namespace BuildState

/-- The graph event produced by a source `sample`. -/
@[reducible] noncomputable def sampleEvent
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1) :
    EventNode P L :=
  let graphDist := eventDistOf state dist normalized
  { ty := graphDist.ty, owner := none, sem := .sample graphDist }

/-- The graph event produced by a source `commit`. -/
@[reducible] noncomputable def commitEvent
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool) : EventNode P L :=
  let graphGuard := eventGuardOf state who guard
  { ty := graphGuard.ty, owner := some who,
    sem := .commit who graphGuard }

/-- The graph event produced by a source `reveal`. -/
@[reducible] def revealEvent
    {Γ : VCtx P L} {sourceName : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (sourceProof : VHasVar Γ sourceName (.sealed who ty)) :
    EventNode P L :=
  { ty := ty, owner := none, sem := .reveal (state.fieldOf sourceProof) }

theorem sampleEvent_nodeWFAt
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1) :
    ({ initialFields := state.initialFields,
       nodes := state.nodes ++ [sampleEvent state dist normalized] } :
      Graph P L).nodeWFAt state.nextNode
        (sampleEvent state dist normalized) := by
  let graphDist := eventDistOf state dist normalized
  let event := sampleEvent state dist normalized
  dsimp [Graph.nodeWFAt, sampleEvent, event, graphDist]
  exact
    ⟨by
        intro field hfield
        rcases Finset.mem_image.mp hfield with ⟨ref, href, rfl⟩
        exact Graph.fieldAvailableBefore_append_node_of_true
          state.initialFields state.nodes event
          (distReadRefs_available state dist ref href),
      rfl, rfl,
      by
        intro ref href
        exact Graph.fieldRefPublic_append_node
          state.initialFields state.nodes event
          (distReadRefs_public state dist ref href)⟩

theorem commitEvent_nodeWFAt
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool) :
    ({ initialFields := state.initialFields,
       nodes := state.nodes ++ [commitEvent state who guard] } :
      Graph P L).nodeWFAt state.nextNode
        (commitEvent state who guard) := by
  let graphGuard := eventGuardOf state who guard
  let event := commitEvent state who guard
  dsimp [Graph.nodeWFAt, commitEvent, event, graphGuard]
  exact
    ⟨by
        intro field hfield
        rcases Finset.mem_image.mp hfield with ⟨ref, href, rfl⟩
        exact Graph.fieldAvailableBefore_append_node_of_true
          state.initialFields state.nodes event
          (visibleFieldRefs_available state who ref href),
      rfl, rfl,
      by
        intro ref href
        exact Graph.fieldRefVisibleTo_append_node
          state.initialFields state.nodes event who
          (visibleFieldRefs_visible state who ref href)⟩

theorem revealEvent_nodeWFAt
    {Γ : VCtx P L} {sourceName : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (sourceProof : VHasVar Γ sourceName (.sealed who ty)) :
    ({ initialFields := state.initialFields,
       nodes := state.nodes ++ [revealEvent state who sourceProof] } :
      Graph P L).nodeWFAt state.nextNode
        (revealEvent state who sourceProof) := by
  let event := revealEvent state who sourceProof
  rcases state.fieldOf_spec sourceProof with
    ⟨sourceSpec, hsource, hty, howner⟩
  dsimp [Graph.nodeWFAt, revealEvent, event]
  rw [Graph.field?_append_node_of_some
    state.initialFields state.nodes
    { ty := ty, owner := none,
      sem := NodeSem.reveal (state.fieldOf sourceProof) }
    hsource]
  refine ⟨?_, sourceSpec, rfl, hty, ?_, rfl⟩
  · intro field hfield
    have hfieldEq : field = state.fieldOf sourceProof :=
      Finset.mem_singleton.mp hfield
    subst hfieldEq
    exact Graph.fieldAvailableBefore_append_node_of_true
      state.initialFields state.nodes event
      (state.fieldOf_available sourceProof)
  · simp [howner]

/-- Compile and append a source `sample` event. -/
@[reducible] noncomputable def addSampleEvent
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1)
    (fresh : Fresh name Γ) :
    BuildState P L ((name, .pub ty) :: Γ) × Nat :=
  let graphDist := eventDistOf state dist normalized
  state.addEvent name (.pub graphDist.ty) (.sample graphDist) fresh
    (sampleEvent_nodeWFAt state dist normalized)

/-- Compile and append a source `commit` event. -/
@[reducible] noncomputable def addCommitEvent
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool)
    (fresh : Fresh name Γ) :
    BuildState P L ((name, .sealed who actionTy) :: Γ) × Nat :=
  let graphGuard := eventGuardOf state who guard
  state.addEvent name (.sealed who graphGuard.ty)
      (.commit who graphGuard) fresh
      (commitEvent_nodeWFAt state who guard)

/-- Compile and append a source `reveal` event. -/
@[reducible] def addRevealEvent
    {Γ : VCtx P L} {sourceName : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (sourceProof : VHasVar Γ sourceName (.sealed who ty))
    (fresh : Fresh name Γ) :
    BuildState P L ((name, .pub ty) :: Γ) × Nat :=
  state.addEvent name (.pub ty)
    (.reveal (state.fieldOf sourceProof)) fresh
    (revealEvent_nodeWFAt state who sourceProof)

@[simp] theorem addSampleEvent_nodes
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1)
    (fresh : Fresh name Γ) :
    (state.addSampleEvent name dist normalized fresh).1.nodes =
      state.nodes ++ [sampleEvent state dist normalized] :=
  rfl

@[simp] theorem addCommitEvent_nodes
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool)
    (fresh : Fresh name Γ) :
    (state.addCommitEvent name who guard fresh).1.nodes =
      state.nodes ++ [commitEvent state who guard] :=
  rfl

@[simp] theorem addRevealEvent_nodes
    {Γ : VCtx P L} {sourceName : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (sourceProof : VHasVar Γ sourceName (.sealed who ty))
    (fresh : Fresh name Γ) :
    (state.addRevealEvent name who sourceProof fresh).1.nodes =
      state.nodes ++ [revealEvent state who sourceProof] :=
  rfl

@[simp] theorem addSampleEvent_initialFields
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1)
    (fresh : Fresh name Γ) :
    (state.addSampleEvent name dist normalized fresh).1.initialFields =
      state.initialFields :=
  rfl

@[simp] theorem addCommitEvent_initialFields
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool)
    (fresh : Fresh name Γ) :
    (state.addCommitEvent name who guard fresh).1.initialFields =
      state.initialFields :=
  rfl

@[simp] theorem addRevealEvent_initialFields
    {Γ : VCtx P L} {sourceName : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (sourceProof : VHasVar Γ sourceName (.sealed who ty))
    (fresh : Fresh name Γ) :
    (state.addRevealEvent name who sourceProof fresh).1.initialFields =
      state.initialFields :=
  rfl

@[simp] theorem addSampleEvent_fieldOf_here
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1)
    (fresh : Fresh name Γ) :
    (state.addSampleEvent name dist normalized fresh).1.fieldOf
        (VHasVar.here (x := name) (τ := .pub ty)) =
      state.nextField :=
  rfl

@[simp] theorem addSampleEvent_fieldOf_there
    {Γ : VCtx P L} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (normalized :
      ∀ depEnv : (x : VarId) → (τ : L.Ty) →
          HasVar (erasePubVCtx Γ) x τ → x ∈ L.distDeps dist → L.Val τ,
        FWeight.totalWeight (L.evalDistDeps dist depEnv) = 1)
    (fresh : Fresh name Γ)
    {query : VarId} {bindTy : BindTy P L}
    (h : VHasVar Γ query bindTy) :
    (state.addSampleEvent name dist normalized fresh).1.fieldOf
        (VHasVar.there h) = state.fieldOf h :=
  rfl

@[simp] theorem addCommitEvent_fieldOf_here
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool)
    (fresh : Fresh name Γ) :
    (state.addCommitEvent name who guard fresh).1.fieldOf
        (VHasVar.here (x := name) (τ := .sealed who actionTy)) =
      state.nextField :=
  rfl

@[simp] theorem addCommitEvent_fieldOf_there
    {Γ : VCtx P L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (guard : L.Expr ((actionName, actionTy) ::
      eraseVCtx (viewVCtx who Γ)) L.bool)
    (fresh : Fresh name Γ)
    {query : VarId} {bindTy : BindTy P L}
    (h : VHasVar Γ query bindTy) :
    (state.addCommitEvent name who guard fresh).1.fieldOf
        (VHasVar.there h) = state.fieldOf h :=
  rfl

@[simp] theorem addRevealEvent_fieldOf_here
    {Γ : VCtx P L} {sourceName : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (sourceProof : VHasVar Γ sourceName (.sealed who ty))
    (fresh : Fresh name Γ) :
    (state.addRevealEvent name who sourceProof fresh).1.fieldOf
        (VHasVar.here (x := name) (τ := .pub ty)) =
      state.nextField :=
  rfl

@[simp] theorem addRevealEvent_fieldOf_there
    {Γ : VCtx P L} {sourceName : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (name : VarId) (who : P)
    (sourceProof : VHasVar Γ sourceName (.sealed who ty))
    (fresh : Fresh name Γ)
    {query : VarId} {bindTy : BindTy P L}
    (h : VHasVar Γ query bindTy) :
    (state.addRevealEvent name who sourceProof fresh).1.fieldOf
        (VHasVar.there h) = state.fieldOf h :=
  rfl

end BuildState

theorem guardLive_empty (initialFields : List (InitialField P L)) :
    GuardLive ({ initialFields := initialFields, nodes := [] } : Graph P L) := by
  intro node _row _who _guard _hrow _hsem _env
  have hlt : (node : Nat) < 0 := by
    simpa [Graph.nodeCount] using node.isLt
  omega

theorem guardLive_append_event
    (initialFields : List (InitialField P L))
    (nodes : List (EventNode P L)) (event : EventNode P L)
    (oldLive :
      GuardLive
        ({ initialFields := initialFields, nodes := nodes } : Graph P L))
    (newLive :
      ∀ {who guard}, event.sem = .commit who guard →
        ∀ env : ReadEnv L guard.choiceReads,
          ∃ value : L.Val guard.ty, guard.eval value env = true) :
    GuardLive
      ({ initialFields := initialFields, nodes := nodes ++ [event] } :
        Graph P L) := by
  intro node row who guard hrow hsem env
  by_cases hlt : (node : Nat) < nodes.length
  · let oldNode :
        Fin (({ initialFields := initialFields, nodes := nodes } :
          Graph P L).nodeCount) :=
      ⟨node, by simpa [Graph.nodeCount] using hlt⟩
    have hold : nodes[(node : Nat)]? = some row := by
      change (nodes ++ [event])[(node : Nat)]? = some row at hrow
      rw [List.getElem?_append_left hlt] at hrow
      exact hrow
    exact oldLive (node := oldNode) (row := row) hold hsem env
  · have hidx : (node : Nat) < (nodes ++ [event]).length := by
      simpa [Graph.nodeCount] using node.isLt
    have hnodeEq : (node : Nat) = nodes.length := by
      simp only [List.length_append, List.length_singleton] at hidx
      omega
    have hrowEq : row = event := by
      change (nodes ++ [event])[(node : Nat)]? = some row at hrow
      rw [hnodeEq, List.getElem?_concat_length] at hrow
      exact (Option.some.inj hrow).symm
    subst hrowEq
    exact newLive hsem env

/-- Every initial field in a list has a finite value domain. -/
def InitialFieldsFinite (fields : List (InitialField P L)) : Type :=
  ∀ field, field ∈ fields → Fintype (L.Val field.ty)

namespace InitialFieldsFinite

noncomputable def nil : InitialFieldsFinite ([] : List (InitialField P L)) := by
  intro field hmem
  simp at hmem

noncomputable def append
    {fields : List (InitialField P L)}
    (finite : InitialFieldsFinite fields)
    (field : InitialField P L) [h : Fintype (L.Val field.ty)] :
    InitialFieldsFinite (fields ++ [field]) := by
  classical
  intro query hmem
  by_cases hquery : query = field
  · cases hquery
    exact h
  · have hold : query ∈ fields := by
      have hcases : query ∈ fields ∨ query ∈ [field] := by
        simpa [List.mem_append] using hmem
      exact hcases.resolve_right (by
        intro hsingle
        exact hquery (by simpa using hsingle))
    exact finite query hold

end InitialFieldsFinite

/-- Initial graph fields come from the checked program's initial context. -/
def initialState :
    (Γ : VCtx P L) → VEnv L Γ → WFCtx Γ → InitialState P L Γ
  | [], _, _ => InitialState.empty
  | (name, bindTy) :: Γ, env, hctx =>
      let tail := initialState Γ (VEnv.tail env) (WFCtx.tail hctx)
      let value : L.Val bindTy.base :=
        VEnv.get env (VHasVar.here (x := name) (τ := bindTy))
      (tail.addField name bindTy value (WFCtx.fresh_head hctx)).1

/-- Finite source contexts induce finite value domains for every initial graph
field allocated from the source environment. -/
noncomputable def initialState_initialFieldsFinite :
    {Γ : VCtx P L} → (env : VEnv L Γ) → (wctx : WFCtx Γ) →
      FiniteVCtxProof Γ →
      InitialFieldsFinite (initialState Γ env wctx).initialFields
  | [], _env, _wctx, .nil =>
      InitialFieldsFinite.nil
  | (name, bindTy) :: Γ, env, hctx, .cons head tailFinite =>
      let tail := initialState Γ (VEnv.tail env) (WFCtx.tail hctx)
      let value : L.Val bindTy.base :=
        VEnv.get env (VHasVar.here (x := name) (τ := bindTy))
      let field : InitialField P L :=
        { ty := bindTy.base, owner := bindTy.owner, value := value }
      let tailFieldsFinite :
          InitialFieldsFinite tail.initialFields :=
        initialState_initialFieldsFinite (VEnv.tail env)
          (WFCtx.tail hctx) tailFinite
      by
        letI : Fintype (L.Val field.ty) := by
          dsimp [field]
          exact head.fintype
        simpa [initialState, InitialState.addField, tail, value, field]
          using InitialFieldsFinite.append tailFieldsFinite field

/-- Compile terminal payoff expressions. -/
noncomputable def compilePayoffs
    {Γ : VCtx P L}
    (state : BuildState P L Γ) :
    List (P × L.Expr (erasePubVCtx Γ) L.int) →
      List (P × EventPayoff L)
  | [] => []
  | payoff :: rest =>
      let expr := eventPayoffOf state payoff.2
      let rest := compilePayoffs state rest
      (payoff.1, expr) :: rest

/-- Result of compiling the linear program body. -/
structure BuildResult (P : Type) [DecidableEq P] (L : IExpr) where
  initialFields : List (InitialField P L)
  nodes : List (EventNode P L)
  graphWF :
    ({ initialFields := initialFields, nodes := nodes } : Graph P L).WF
  payoffs : List (P × EventPayoff L)
  payoffsWF :
    ∀ payoff, payoff ∈ payoffs →
      ∀ ref, ref ∈ payoff.2.reads →
        ({ initialFields := initialFields, nodes := nodes } :
          Graph P L).fieldRefPublic ref ∧
        ({ initialFields := initialFields, nodes := nodes } :
          Graph P L).fieldAvailableBefore nodes.length ref.field = true
  terminalCtx : VCtx P L
  terminalState : BuildState P L terminalCtx
  sourcePayoffs : List (P × L.Expr (erasePubVCtx terminalCtx) L.int)
  terminalInitialFields :
    terminalState.initialFields = initialFields
  terminalNodes :
    terminalState.nodes = nodes
  payoffs_eq :
    payoffs = compilePayoffs terminalState sourcePayoffs

namespace BuildResult

def graph (result : BuildResult P L) : Graph P L :=
  { initialFields := result.initialFields, nodes := result.nodes }

theorem terminal_graph_eq (result : BuildResult P L) :
    ({ initialFields := result.terminalState.initialFields,
       nodes := result.terminalState.nodes } : Graph P L) =
      result.graph := by
  rcases result with
    ⟨initialFields, nodes, graphWF, payoffs, payoffsWF,
      terminalCtx, terminalState, sourcePayoffs, hinitial, hnodes,
      hpayoffs⟩
  simp [graph, hinitial, hnodes]

end BuildResult

/-- Every event row in a node list has a finite output value domain. -/
def NodesFinite (nodes : List (EventNode P L)) : Type :=
  ∀ row, row ∈ nodes → Fintype (L.Val row.ty)

namespace NodesFinite

noncomputable def nil : NodesFinite ([] : List (EventNode P L)) := by
  intro row hmem
  simp at hmem

noncomputable def append
    {nodes : List (EventNode P L)} (finite : NodesFinite nodes)
    (event : EventNode P L) [h : Fintype (L.Val event.ty)] :
    NodesFinite (nodes ++ [event]) := by
  classical
  intro row hmem
  by_cases hrow : row = event
  · cases hrow
    exact h
  · have hold : row ∈ nodes := by
      have hcases : row ∈ nodes ∨ row ∈ [event] := by
        simpa [List.mem_append] using hmem
      exact hcases.resolve_right (by
        intro hsingle
        exact hrow (by simpa using hsingle))
    exact finite row hold

@[reducible] noncomputable def nodeFintype
    {initialFields : List (InitialField P L)}
    {nodes : List (EventNode P L)}
    (finite : NodesFinite nodes) :
    ∀ node : Fin (({ initialFields := initialFields, nodes := nodes } :
      Graph P L).nodeCount),
      Fintype (L.Val
        (({ initialFields := initialFields, nodes := nodes } :
          Graph P L).nodeRow node).ty) := by
  intro node
  let graph : Graph P L :=
    { initialFields := initialFields, nodes := nodes }
  have hget :
      nodes[(node : Nat)]? = some (graph.nodeRow node) := by
    simpa [graph] using graph.nodes_get?_nodeRow node
  exact finite (graph.nodeRow node) (List.mem_of_getElem? hget)

end NodesFinite

@[reducible] noncomputable def fieldFintypeOfInitialAndNodes
    {initialFields : List (InitialField P L)}
    {nodes : List (EventNode P L)}
    (finiteInitial : InitialFieldsFinite initialFields)
    (finiteNodes : NodesFinite nodes) :
    ∀ field : Fin (({ initialFields := initialFields, nodes := nodes } :
      Graph P L).fieldCount),
      Fintype (L.Val
        (({ initialFields := initialFields, nodes := nodes } :
          Graph P L).fieldRow field).ty) := by
  classical
  intro field
  by_cases hinit : (field : Nat) < initialFields.length
  · simpa only [Graph.fieldRow, hinit, ↓reduceDIte] using
      finiteInitial initialFields[(field : Nat)] (List.getElem_mem _)
  · let node : Nat := (field : Nat) - initialFields.length
    have hnode : node < nodes.length := by
      have hlt : (field : Nat) < initialFields.length + nodes.length := by
        have hlt' := field.isLt
        change (field : Nat) < initialFields.length + nodes.length at hlt'
        exact hlt'
      dsimp [node]
      omega
    simp only [Graph.fieldRow, hinit, ↓reduceDIte]
    exact finiteNodes nodes[node] (List.getElem_mem _)

@[simp] theorem compilePayoffs_length
    {Γ : VCtx P L}
    (state : BuildState P L Γ) :
    ∀ payoffs,
      (compilePayoffs state payoffs).length = payoffs.length
  | [] => rfl
  | _ :: rest => by
      simp [compilePayoffs, compilePayoffs_length state rest]

/-- Compiled payoff-entry evaluation agrees with source payoff-entry
evaluation when each compiled payoff read environment agrees with a source
public environment on the source expression's declared dependencies. -/
theorem evalPayoffEntries?_compilePayoffs_eq_source
    {Γ : VCtx P L}
    (state : BuildState P L Γ)
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int))
    (sourceEnv : Env L.Val (erasePubVCtx Γ))
    (store : Store L)
    (hagrees :
      ∀ payoff, payoff ∈ payoffs →
        ∃ readEnv,
          ReadEnv.ofStore? store (eventPayoffOf state payoff.2).reads =
            some readEnv ∧
          ∀ {name ty} (hvar : HasVar (erasePubVCtx Γ) name ty)
            (hmem : name ∈ L.exprDeps payoff.2),
            sourceValuePub state readEnv hvar
              (exprReadRefs_mem state payoff.2 hvar hmem) =
              sourceEnv name ty hvar) :
    evalPayoffEntries? (compilePayoffs state payoffs) store =
      some (payoffs.map fun payoff =>
        (payoff.1, L.toInt (L.eval payoff.2 sourceEnv))) := by
  induction payoffs with
  | nil =>
      rfl
  | cons payoff rest ih =>
      rcases hagrees payoff (by simp) with
        ⟨readEnv, hreadEnv, hreadAgrees⟩
      have hhead :
          (eventPayoffOf state payoff.2).eval readEnv =
            L.toInt (L.eval payoff.2 sourceEnv) :=
        eventPayoffOf_eval_eq_eval
          state payoff.2 sourceEnv readEnv hreadAgrees
      have htail :
          evalPayoffEntries? (compilePayoffs state rest) store =
            some (rest.map fun payoff =>
              (payoff.1, L.toInt (L.eval payoff.2 sourceEnv))) := by
        exact ih (by
          intro tailPayoff htailMem
          exact hagrees tailPayoff (by simp [htailMem]))
      simp [compilePayoffs, evalPayoffEntries?, hreadEnv, hhead, htail]

/-- Compiled payoff evaluation agrees with source `evalPayoffs` when every
compiled payoff projection reads the same public source values as the terminal
source environment. -/
theorem evalPayoffs?_compilePayoffs_eq_source
    {Γ : VCtx P L}
    (state : BuildState P L Γ)
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int))
    (sourceEnv : VEnv L Γ)
    (store : Store L)
    (hagrees :
      ∀ payoff, payoff ∈ payoffs →
        ∃ readEnv,
          ReadEnv.ofStore? store (eventPayoffOf state payoff.2).reads =
            some readEnv ∧
          ∀ {name ty} (hvar : HasVar (erasePubVCtx Γ) name ty)
            (hmem : name ∈ L.exprDeps payoff.2),
            sourceValuePub state readEnv hvar
              (exprReadRefs_mem state payoff.2 hvar hmem) =
              VEnv.erasePubEnv sourceEnv name ty hvar) :
    evalPayoffs? (compilePayoffs state payoffs) store =
      some (evalPayoffs payoffs sourceEnv) := by
  have hentries :=
    evalPayoffEntries?_compilePayoffs_eq_source
      state payoffs (VEnv.erasePubEnv sourceEnv) store hagrees
  simp [evalPayoffs?, hentries, evalPayoffs]

/-- Compiled payoff evaluation agrees with source payoff evaluation for the
source environment reconstructed from the terminal graph store. -/
theorem evalPayoffs?_compilePayoffs_eq_sourceEnvOfStore
    {Γ : VCtx P L}
    (state : BuildState P L Γ)
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int))
    (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value) :
    evalPayoffs? (compilePayoffs state payoffs) store =
      some (evalPayoffs payoffs
        (sourceEnvOfStore state store available)) := by
  exact
    evalPayoffs?_compilePayoffs_eq_source state payoffs
      (sourceEnvOfStore state store available) store
      (by
        intro payoff _hpayoff
        exact eventPayoffOf_readEnv_agrees_sourceEnvOfStore
          state payoff.2 store available)

theorem compilePayoffs_wf
    {Γ : VCtx P L}
    (state : BuildState P L Γ) :
    ∀ payoffs payoff, payoff ∈ compilePayoffs state payoffs →
      ∀ ref, ref ∈ payoff.2.reads →
        ({ initialFields := state.initialFields, nodes := state.nodes } :
          Graph P L).fieldRefPublic ref ∧
        ({ initialFields := state.initialFields, nodes := state.nodes } :
          Graph P L).fieldAvailableBefore state.nodes.length ref.field = true
  | [], payoff, hmem => by
      simp [compilePayoffs] at hmem
  | sourcePayoff :: rest, payoff, hmem => by
      change
        payoff ∈
          (sourcePayoff.1, eventPayoffOf state sourcePayoff.2) ::
            compilePayoffs state rest at hmem
      rw [List.mem_cons] at hmem
      cases hmem with
      | inl hhead =>
          subst payoff
          intro ref href
          exact
            ⟨exprReadRefs_public state sourcePayoff.2 ref href,
              exprReadRefs_available state sourcePayoff.2 ref href⟩
      | inr htail =>
          exact compilePayoffs_wf state rest payoff htail

/-- Compile a checked core program suffix into fields and nodes. -/
noncomputable def compileCore :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      FreshBindings prog → NormalizedDists prog → BuildState P L Γ →
      BuildResult P L
  | _, .ret payoffs, _fresh, _normalized, state =>
      let compiledPayoffs := compilePayoffs state payoffs
      { initialFields := state.initialFields, nodes := state.nodes,
        graphWF := state.graphWF, payoffs := compiledPayoffs,
        payoffsWF := by
          intro payoff hpayoff ref href
          exact compilePayoffs_wf state payoffs payoff hpayoff ref href
        terminalCtx := _
        terminalState := state
        sourcePayoffs := payoffs
        terminalInitialFields := rfl
        terminalNodes := rfl
        payoffs_eq := rfl }
  | _, .sample name dist tail, fresh, normalized, state =>
      let added :=
        state.addSampleEvent name dist normalized.1 fresh.1
      let state := added.1
      compileCore tail fresh.2 normalized.2 state
  | _, .commit name who guard tail, fresh, normalized, state =>
      let added :=
        state.addCommitEvent name who guard fresh.1
      let state := added.1
      compileCore tail fresh.2 normalized state
  | _, .reveal (b := ty) name _who _source sourceProof tail, fresh, normalized, state =>
      let added :=
        state.addRevealEvent name _who sourceProof fresh.1
      let state := added.1
      compileCore tail fresh.2 normalized state

@[simp] theorem compileCore_initialFields :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (normalized : NormalizedDists prog) →
      (state : BuildState P L Γ) →
      (compileCore prog fresh normalized state).initialFields =
        state.initialFields
  | _, .ret _payoffs, _fresh, _normalized, _state => rfl
  | _, .sample name dist tail, fresh, normalized, state => by
      let added :=
        state.addSampleEvent name dist normalized.1 fresh.1
      change
        (compileCore tail fresh.2 normalized.2 added.1).initialFields =
          state.initialFields
      rw [compileCore_initialFields tail fresh.2 normalized.2 added.1]
      exact BuildState.addSampleEvent_initialFields
        state name dist normalized.1 fresh.1
  | _, .commit name who guard tail, fresh, normalized, state => by
      let added :=
        state.addCommitEvent name who guard fresh.1
      change
        (compileCore tail fresh.2 normalized added.1).initialFields =
          state.initialFields
      rw [compileCore_initialFields tail fresh.2 normalized added.1]
      exact BuildState.addCommitEvent_initialFields
        state name who guard fresh.1
  | _, .reveal (b := ty) name _who _source sourceProof tail,
      fresh, normalized, state => by
      let added :=
        state.addRevealEvent name _who sourceProof fresh.1
      change
        (compileCore tail fresh.2 normalized added.1).initialFields =
          state.initialFields
      rw [compileCore_initialFields tail fresh.2 normalized added.1]
      exact BuildState.addRevealEvent_initialFields
        state name _who sourceProof fresh.1

/-- Finite source operational domains induce finite value domains for every
compiled graph node. -/
noncomputable def compileCore_nodesFinite :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      FiniteProgramProof prog →
      (fresh : FreshBindings prog) → (normalized : NormalizedDists prog) →
      (state : BuildState P L Γ) → NodesFinite state.nodes →
      let result := compileCore prog fresh normalized state
      NodesFinite result.nodes
  | _, .ret _payoffs, _finite, _fresh, _normalized, _state, stateFinite =>
      stateFinite
  | _, .sample name dist tail, .sample head tailFinite,
      fresh, normalized, state, stateFinite =>
      let event : EventNode P L :=
        state.sampleEvent dist normalized.1
      let added :=
        state.addSampleEvent name dist normalized.1 fresh.1
      let eventFinite : Fintype (L.Val event.ty) := by
        dsimp [event, BuildState.sampleEvent, eventDistOf]
        exact head.fintype
      let addedFinite : NodesFinite added.1.nodes := by
        dsimp only [added]
        rw [BuildState.addSampleEvent_nodes]
        letI : Fintype (L.Val event.ty) := eventFinite
        exact NodesFinite.append stateFinite event
      compileCore_nodesFinite tail tailFinite fresh.2 normalized.2
        added.1 addedFinite
  | _, .commit name who guard tail, .commit head tailFinite,
      fresh, normalized, state, stateFinite =>
      let event : EventNode P L :=
        state.commitEvent who guard
      let added :=
        state.addCommitEvent name who guard fresh.1
      let eventFinite : Fintype (L.Val event.ty) := by
        dsimp [event, BuildState.commitEvent, eventGuardOf]
        exact head.fintype
      let addedFinite : NodesFinite added.1.nodes := by
        dsimp only [added]
        rw [BuildState.addCommitEvent_nodes]
        letI : Fintype (L.Val event.ty) := eventFinite
        exact NodesFinite.append stateFinite event
      compileCore_nodesFinite tail tailFinite fresh.2 normalized
        added.1 addedFinite
  | _, .reveal (b := ty) name _who _source sourceProof tail,
      .reveal head tailFinite, fresh, normalized, state, stateFinite =>
      let event : EventNode P L :=
        state.revealEvent _who sourceProof
      let added :=
        state.addRevealEvent name _who sourceProof fresh.1
      let eventFinite : Fintype (L.Val event.ty) := by
        dsimp [event, BuildState.revealEvent]
        exact head.fintype
      let addedFinite : NodesFinite added.1.nodes := by
        dsimp only [added]
        rw [BuildState.addRevealEvent_nodes]
        letI : Fintype (L.Val event.ty) := eventFinite
        exact NodesFinite.append stateFinite event
      compileCore_nodesFinite tail tailFinite fresh.2 normalized
        added.1 addedFinite

/-- Source guard legality compiles to graph guard liveness for every commit
node produced by a program suffix, assuming the nodes already present in the
compiler state are live. -/
theorem compileCore_guardLive :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (normalized : NormalizedDists prog) →
      (state : BuildState P L Γ) →
      GuardLive
        ({ initialFields := state.initialFields, nodes := state.nodes } :
          Graph P L) →
      Legal prog →
      let result := compileCore prog fresh normalized state
      GuardLive
        ({ initialFields := result.initialFields, nodes := result.nodes } :
          Graph P L)
  | _, .ret _payoffs, _fresh, _normalized, _state, stateLive, _legal =>
      stateLive
  | _, .sample name dist tail, fresh, normalized, state, stateLive, legal =>
      let event : EventNode P L :=
        state.sampleEvent dist normalized.1
      let added :=
        state.addSampleEvent name dist normalized.1 fresh.1
      let addedLive :
          GuardLive
            ({ initialFields := added.1.initialFields,
               nodes := added.1.nodes } : Graph P L) := by
        dsimp only [added]
        rw [BuildState.addSampleEvent_initialFields,
          BuildState.addSampleEvent_nodes]
        exact guardLive_append_event
          state.initialFields state.nodes event stateLive
          (by
            intro who guard hsem _env
            cases hsem)
      compileCore_guardLive tail fresh.2 normalized.2 added.1
        addedLive legal
  | _, .commit name who guard tail, fresh, normalized, state, stateLive, legal =>
      let event : EventNode P L :=
        state.commitEvent who guard
      let added :=
        state.addCommitEvent name who guard fresh.1
      let addedLive :
          GuardLive
            ({ initialFields := added.1.initialFields,
               nodes := added.1.nodes } : Graph P L) := by
        dsimp only [added]
        rw [BuildState.addCommitEvent_initialFields,
          BuildState.addCommitEvent_nodes]
        exact guardLive_append_event
          state.initialFields state.nodes event stateLive
          (by
            intro actor graphGuard' hsem env
            cases hsem
            exact eventGuardOf_live_of_legal state who guard legal.1 env)
      compileCore_guardLive tail fresh.2 normalized added.1
        addedLive legal.2
  | _, .reveal (b := ty) name _who _source sourceProof tail,
      fresh, normalized, state, stateLive, legal =>
      let event : EventNode P L :=
        state.revealEvent _who sourceProof
      let added :=
        state.addRevealEvent name _who sourceProof fresh.1
      let addedLive :
          GuardLive
            ({ initialFields := added.1.initialFields,
               nodes := added.1.nodes } : Graph P L) := by
        dsimp only [added]
        rw [BuildState.addRevealEvent_initialFields,
          BuildState.addRevealEvent_nodes]
        exact guardLive_append_event
          state.initialFields state.nodes event stateLive
          (by
            intro who guard hsem _env
            cases hsem)
      compileCore_guardLive tail fresh.2 normalized added.1
        addedLive legal

/-- A compiled checked program: graph plus terminal payoff projection. -/
structure CompiledProgram (P : Type) [DecidableEq P] (L : IExpr) where
  private mk ::
  graph : EventGraph.Graph P L
  graphWF : graph.WF
  payoffs : List (P × EventPayoff L)
  payoffsWF :
    ∀ payoff, payoff ∈ payoffs →
      ∀ ref, ref ∈ payoff.2.reads →
        graph.fieldRefPublic ref ∧
        graph.fieldAvailableBefore graph.nodeCount ref.field = true

/-- Compile a graph-program to graph data plus the terminal source context
certificate used by source-level adequacy theorems. -/
noncomputable def buildResult (g : GraphProgram P L) : BuildResult P L :=
  let init := initialState g.Γ g.env g.wctx
  compileCore g.prog g.fresh g.normalized (BuildState.fromInitial init)

/-- Compile a graph-program to the canonical event graph representation. -/
noncomputable def compile (g : GraphProgram P L) : CompiledProgram P L :=
  let init := initialState g.Γ g.env g.wctx
  let result := compileCore g.prog g.fresh g.normalized (BuildState.fromInitial init)
  let graph : EventGraph.Graph P L :=
    { initialFields := result.initialFields, nodes := result.nodes }
  {
    graph := graph
    graphWF := result.graphWF
    payoffs := result.payoffs
    payoffsWF := by
      intro payoff hpayoff ref href
      exact result.payoffsWF payoff hpayoff ref href }

/-- Finite checked programs compile to graphs whose node action/value domains
are finite. This is the exact evidence needed to instantiate finite frontier
round action alphabets. -/
@[reducible] noncomputable def compile_nodeFintype
    (program : WFProgram P L) [domains : FiniteDomains program] :
    ∀ node : Fin (compile program.core).graph.nodeCount,
      Fintype (L.Val ((compile program.core).graph.nodeRow node).ty) := by
  unfold compile
  let init := initialState program.core.Γ program.core.env program.core.wctx
  let state := BuildState.fromInitial init
  let result :=
    compileCore program.core.prog program.core.fresh
      program.core.normalized state
  have finiteNodes : NodesFinite result.nodes :=
    compileCore_nodesFinite
      program.core.prog
      domains.program.proof
      program.core.fresh
      program.core.normalized
      state
      NodesFinite.nil
  exact NodesFinite.nodeFintype finiteNodes

/-- Finite checked programs compile to graphs whose finite field ids all have
finite value domains. This includes both initial source fields and event
output fields. -/
@[reducible] noncomputable def compile_fieldFintype
    (program : WFProgram P L) [domains : FiniteDomains program] :
    ∀ field : Fin (compile program.core).graph.fieldCount,
      Fintype (L.Val ((compile program.core).graph.fieldRow field).ty) := by
  unfold compile
  let init := initialState program.core.Γ program.core.env program.core.wctx
  let state := BuildState.fromInitial init
  let result :=
    compileCore program.core.prog program.core.fresh
      program.core.normalized state
  have finiteInitial : InitialFieldsFinite result.initialFields := by
    have hinit :
        InitialFieldsFinite state.initialFields := by
      simpa [state, BuildState.fromInitial] using
        initialState_initialFieldsFinite program.core.env program.core.wctx
          domains.context.proof
    have hresult :
        result.initialFields = state.initialFields :=
      compileCore_initialFields
        program.core.prog program.core.fresh program.core.normalized state
    rw [hresult]
    exact hinit
  have finiteNodes : NodesFinite result.nodes :=
    compileCore_nodesFinite
      program.core.prog
      domains.program.proof
      program.core.fresh
      program.core.normalized
      state
      NodesFinite.nil
  exact fieldFintypeOfInitialAndNodes finiteInitial finiteNodes

/-- Checked source guard legality compiles to graph-level guard liveness. -/
theorem compile_guardLive (program : WFProgram P L) :
    EventGraph.GuardLive (compile program.core).graph := by
  unfold compile
  exact
    compileCore_guardLive
      program.core.prog
      program.core.fresh
      program.core.normalized
      (BuildState.fromInitial
        (initialState program.core.Γ program.core.env program.core.wctx))
      (guardLive_empty
        (BuildState.fromInitial
          (initialState program.core.Γ program.core.env
            program.core.wctx)).initialFields)
      program.legal

end ToEventGraph

end Vegas
