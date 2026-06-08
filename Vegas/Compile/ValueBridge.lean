/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceBridge
import Vegas.Core.Trace

/-!
# Source-to-graph bridge: the value dimension

The structural bridge (`Vegas.Compile.SourceBridge`) ties the compiled graph's
*shape* — node count, owners, readable order — to the source program. This file
begins the *value* dimension: a source run carries, in its labels, the value
drawn, chosen, or disclosed at each step, and these are the values the graph
nodes receive.

`Label.toTypedValue` packs a label's value as a graph `TypedValue`.
`LabeledStar.length_eq_instrCount_of_terminal` shows a terminal run takes exactly
`instrCount` steps, so — with `compile_graph_nodeCount` — a terminal run from the
initial configuration produces exactly one value per graph node, the raw material
for the per-node value assignment `w` the graph completion consumes.

The deeper claim that completing the graph with these values reproduces the
source's terminal environment (and that the assignment is node-typed, discharging
`StoreCoherent`) is the next milestone; this file lays the counting groundwork.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The value a labelled step produced, packed as a graph `TypedValue`. -/
def Label.toTypedValue : Label P L → EventGraph.TypedValue L
  | .sample _ v => ⟨_, v⟩
  | .commit _ _ v => ⟨_, v⟩
  | .reveal _ _ _ v => ⟨_, v⟩

/-- The source type of the value produced by a labelled step. -/
def Label.ty : Label P L → L.Ty
  | .sample _ (b := b) _ => b
  | .commit _ _ (b := b) _ => b
  | .reveal _ _ _ (b := b) _ => b

omit [DecidableEq P] in
@[simp] theorem Label.toTypedValue_ty (label : Label P L) :
    label.toTypedValue.ty = label.ty := by
  cases label <;> rfl

/-- A labelled step consumes exactly one instruction: the continuation has one
fewer. -/
theorem LStep.instrCount_cont {cfg b : SourceConfig P L} {ℓ : Label P L}
    (h : LStep cfg ℓ b) :
    cfg.cont.instrCount = b.cont.instrCount + 1 := by
  cases h <;> rfl

/-- A labelled step's label type is exactly the type of the instruction it
consumes. -/
theorem LStep.instrTypes_cont {cfg b : SourceConfig P L} {ℓ : Label P L}
    (h : LStep cfg ℓ b) :
    cfg.cont.instrTypes = ℓ.ty :: b.cont.instrTypes := by
  cases h <;> rfl

namespace SourceConfig

/-- A run that reaches a terminal configuration takes exactly as many steps as
the program has instructions. -/
theorem LabeledStar.length_eq_instrCount_of_terminal
    {cfg final : SourceConfig P L} {labels : List (Label P L)}
    (h : SourceConfig.LabeledStar cfg labels final) :
    final.IsTerminal → labels.length = cfg.cont.instrCount := by
  induction h with
  | refl c =>
      intro hterm
      obtain ⟨p, hp⟩ := hterm
      simp [hp, VegasCore.instrCount]
  | cons step _rest ih =>
      intro hterm
      rw [List.length_cons, ih hterm, ← step.instrCount_cont]

/-- A terminal source run records exactly the source instruction output types,
in source execution order. -/
theorem LabeledStar.label_types_eq_instrTypes_of_terminal
    {cfg final : SourceConfig P L} {labels : List (Label P L)}
    (h : SourceConfig.LabeledStar cfg labels final) :
    final.IsTerminal → labels.map Label.ty = cfg.cont.instrTypes := by
  induction h with
  | refl c =>
      intro hterm
      obtain ⟨p, hp⟩ := hterm
      simp [hp, VegasCore.instrTypes]
  | cons step _rest ih =>
      intro hterm
      rw [List.map_cons, ih hterm, step.instrTypes_cont]

/-- A terminal run from the initial configuration produces exactly one label —
hence one value — per source instruction (and per compiled graph node). -/
theorem labeledStar_initial_length {prog : VegasCore P L []}
    {labels : List (Label P L)} {final : SourceConfig P L}
    (h : SourceConfig.LabeledStar (SourceConfig.initial prog) labels final)
    (hterm : final.IsTerminal) :
    labels.length = prog.instrCount := by
  simpa [SourceConfig.initial] using
    h.length_eq_instrCount_of_terminal hterm

end SourceConfig

namespace ToEventGraph

open EventGraph

/-- Store/environment agreement for the source variables tracked by a compiler
state. The predicate is indexed by the source context through `state`; the store
itself is graph-agnostic, so it can be threaded while compilation grows the
graph prefix. -/
def StoreAgree {Γ : VCtx P L} (state : BuildState P L Γ)
    (env : VEnv L Γ) (store : Store L) : Prop :=
  ∀ {name bindTy} (h : VHasVar Γ name bindTy),
    Store.getAs store (state.fieldOf h) bindTy.base = some (env.get h)

/-- The initial compiler state stores exactly the source environment in its
initial fields. The extra `nodes` parameter lets the lemma apply to any later
graph extension, since initial fields are not shifted by appended event nodes. -/
theorem initialState_initialStore_get :
    {Γ : VCtx P L} → (env : VEnv L Γ) → (wctx : WFCtx Γ) →
      (nodes : List (EventNode P L)) →
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        Store.getAs
            (({ initialFields := (initialState Γ env wctx).initialFields,
                nodes := nodes } : Graph P L).initialStore)
            ((initialState Γ env wctx).fieldOf h) bindTy.base =
          some (env.get h)
  | [], _env, _wctx, _nodes, _name, _bindTy, h => by
      cases h
  | (headName, headTy) :: Γ, env, wctx, nodes, _name, _bindTy, h => by
      let tail := initialState Γ (VEnv.tail env) (WFCtx.tail wctx)
      let value : L.Val headTy.base :=
        VEnv.get env (VHasVar.here (x := headName) (τ := headTy))
      let field : InitialField P L :=
        { ty := headTy.base, owner := headTy.owner, value := value }
      cases h with
      | here =>
          simp [initialState, InitialState.addField, InitialState.consFieldOf,
            InitialState.nextField, Graph.initialStore, Graph.field?,
            Store.getAs, FieldSpec.initialValue?, TypedValue.as?]
      | there htail =>
          have hlt : tail.fieldOf htail < tail.initialFields.length :=
            tail.fieldOf_lt htail
          have hle : tail.fieldOf htail ≤ tail.initialFields.length :=
            Nat.le_of_lt hlt
          have ih :=
            initialState_initialStore_get
              (env := VEnv.tail env) (wctx := WFCtx.tail wctx)
              ([] : List (EventNode P L)) htail
          simpa [initialState, InitialState.addField,
            InitialState.consFieldOf, InitialState.nextField, tail,
            Graph.initialStore, Graph.field?, Store.getAs,
            FieldSpec.initialValue?, TypedValue.as?, hlt, hle,
            VEnv.tail, VEnv.get] using ih

/-- Initial source values agree with the graph initial store. -/
theorem StoreAgree_fromInitial_initialStore
    {Γ : VCtx P L} (env : VEnv L Γ) (wctx : WFCtx Γ)
    (nodes : List (EventNode P L)) :
    StoreAgree
      (BuildState.fromInitial (initialState Γ env wctx))
      env
      (({ initialFields := (initialState Γ env wctx).initialFields,
          nodes := nodes } : Graph P L).initialStore) := by
  intro name bindTy h
  simpa [StoreAgree, BuildState.fromInitial] using
    initialState_initialStore_get
      (env := env) (wctx := wctx) nodes h

end ToEventGraph

end Vegas
