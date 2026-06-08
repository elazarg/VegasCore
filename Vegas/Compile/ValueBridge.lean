/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceBridge
import Vegas.Core.Trace
import Vegas.EventGraph.Linearization

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

/-- Store agreement is exactly the condition needed for `sourceEnvOfStore` to
read back the source environment. -/
theorem sourceEnvOfStore_eq_of_storeAgree
    {Γ : VCtx P L} {state : BuildState P L Γ}
    {env : VEnv L Γ} {store : Store L}
    (hagree : StoreAgree state env store)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value, Store.getAs store (state.fieldOf h) bindTy.base =
          some value) :
    sourceEnvOfStore state store available = env := by
  funext name bindTy h
  have hread :=
    sourceEnvOfStore_get state store available h
  exact Option.some.inj (hread.symm.trans (hagree h))

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

/-- Writing the field allocated by `addEvent` extends store agreement from the
old source environment to the environment with the new head binding. -/
theorem StoreAgree.addEvent
    {Γ : VCtx P L} {state : BuildState P L Γ}
    {env : VEnv L Γ} {store : Store L}
    (hagree : StoreAgree state env store)
    (name : VarId) (bindTy : BindTy P L) (sem : NodeSem P L)
    (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
          [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt
        state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem })
    (value : L.Val bindTy.base) :
    StoreAgree
      (state.addEvent name bindTy sem hfresh hnode).1
      (VEnv.cons (x := name) (τ := bindTy) value env)
      (Store.set store state.nextField
        { ty := bindTy.base, value := value }) := by
  intro query queryTy h
  cases h with
  | here =>
      simp [BuildState.addEvent_fieldOf_here, Store.getAs,
        TypedValue.as?]
  | there htail =>
      have hne :
          state.fieldOf htail ≠ state.nextField := by
        have hlt := state.fieldOf_lt htail
        intro heq
        unfold BuildState.nextField BuildState.nextNode at heq
        omega
      rw [BuildState.addEvent_fieldOf_there]
      exact
        (Store.getAs_set_ne store hne
          { ty := bindTy.base, value := value } queryTy.base).trans
          (hagree htail)

/-- A terminal labelled source run can be mirrored by threading graph-store
writes through the compiler state, yielding a terminal store that agrees with
the run's final source environment. This is the lockstep induction spine used by
the canonical-completion representation theorem. -/
theorem StoreAgree_run_exists_compileCore
    {start final : SourceConfig P L} {labels : List (Label P L)}
    (hrun : SourceConfig.LabeledStar start labels final)
    (fresh : FreshBindings start.cont)
    (normalized : NormalizedDists start.cont)
    (state : BuildState P L start.ctx)
    {store : Store L}
    (hagree : StoreAgree state start.env store)
    (hterminal : final.IsTerminal) :
    let result := compileCore start.cont fresh normalized state
    ∃ hctx : final.ctx = result.terminalCtx,
      ∃ terminalStore : Store L,
        StoreAgree result.terminalState
          (cast (congrArg (VEnv L) hctx) final.env)
          terminalStore := by
  induction hrun generalizing store with
  | refl cfg =>
      rcases cfg with ⟨Γ, env, cont⟩
      dsimp [SourceConfig.IsTerminal] at hterminal ⊢
      obtain ⟨payoffs, hpayoffs⟩ := hterminal
      subst cont
      exact ⟨rfl, store, hagree⟩
  | cons step rest ih =>
      cases step with
      | @sample Γ env x b D' k v hv =>
          let graphDist := eventDistOf state D' normalized.1
          let sem := NodeSem.sample (Player := P) graphDist
          let event : EventNode P L :=
            { ty := graphDist.ty, owner := none, sem := sem }
          let hnode :
              ({ initialFields := state.initialFields,
                 nodes := state.nodes ++ [event] } :
                Graph P L).nodeWFAt state.nextNode event := by
            dsimp [Graph.nodeWFAt, graphDist, sem, event]
            exact
              ⟨by
                  intro field hfield
                  rcases Finset.mem_image.mp hfield with ⟨ref, href, rfl⟩
                  exact Graph.fieldAvailableBefore_append_node_of_true
                    state.initialFields state.nodes event
                    (distReadRefs_available state D' ref href),
                rfl, rfl,
                by
                  intro ref href
                  exact Graph.fieldRefPublic_append_node
                    state.initialFields state.nodes event
                    (distReadRefs_public state D' ref href)⟩
          let added :=
            state.addEvent x (.pub graphDist.ty) sem fresh.1 hnode
          have hagree' :
              StoreAgree added.1 (VEnv.cons v env)
                (Store.set store state.nextField
                  { ty := graphDist.ty, value := v }) := by
            exact hagree.addEvent x (.pub graphDist.ty) sem fresh.1 hnode v
          simpa [compileCore, graphDist, sem, event, hnode, added] using
            ih fresh.2 normalized.2 added.1
              (store := Store.set store state.nextField
                { ty := graphDist.ty, value := v })
              hagree' hterminal
      | @commit Γ env x who b R k v hguard =>
          let graphGuard := eventGuardOf state who R
          let sem := NodeSem.commit (Player := P) who graphGuard
          let event : EventNode P L :=
            { ty := graphGuard.ty, owner := some who, sem := sem }
          let hnode :
              ({ initialFields := state.initialFields,
                 nodes := state.nodes ++ [event] } :
                Graph P L).nodeWFAt state.nextNode event := by
            dsimp [Graph.nodeWFAt, graphGuard, sem, event]
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
          let added :=
            state.addEvent x (.sealed who graphGuard.ty) sem fresh.1 hnode
          have hagree' :
              StoreAgree added.1 (VEnv.cons v env)
                (Store.set store state.nextField
                  { ty := graphGuard.ty, value := v }) := by
            exact
              hagree.addEvent x (.sealed who graphGuard.ty) sem fresh.1
                hnode v
          simpa [compileCore, graphGuard, sem, event, hnode, added] using
            ih fresh.2 normalized added.1
              (store := Store.set store state.nextField
                { ty := graphGuard.ty, value := v })
              hagree' hterminal
      | @reveal Γ env y who x b hx k =>
          let sourceField := state.fieldOf hx
          let sem := NodeSem.reveal (Player := P) (L := L) sourceField
          let revealed : L.Val b := VEnv.get env hx
          let event : EventNode P L :=
            { ty := b, owner := none, sem := sem }
          let hnode :
              ({ initialFields := state.initialFields,
                 nodes := state.nodes ++ [event] } :
                Graph P L).nodeWFAt state.nextNode event := by
            rcases state.fieldOf_spec hx with
              ⟨sourceSpec, hsource, hty, howner⟩
            dsimp [Graph.nodeWFAt, sem, event]
            rw [Graph.field?_append_node_of_some
              state.initialFields state.nodes event hsource]
            refine
              ⟨?_, sourceSpec, rfl, hty, ?_, rfl⟩
            · intro field hfield
              have hfieldEq : field = sourceField :=
                Finset.mem_singleton.mp hfield
              subst hfieldEq
              exact Graph.fieldAvailableBefore_append_node_of_true
                state.initialFields state.nodes event
                (state.fieldOf_available hx)
            · simp [howner]
          let added :=
            state.addEvent y (.pub b) sem fresh.1 hnode
          have hagree' :
              StoreAgree added.1 (VEnv.cons revealed env)
                (Store.set store state.nextField
                  { ty := b, value := revealed }) := by
            exact hagree.addEvent y (.pub b) sem fresh.1 hnode revealed
          simpa [compileCore, sourceField, sem, event, hnode, added] using
            ih fresh.2 normalized added.1
              (store := Store.set store state.nextField
                { ty := b, value := revealed })
              hagree' hterminal

/-- Interpret a full source label trace as the per-node value assignment for a
graph with the same node count. -/
noncomputable def labelValueAssignment (G : Graph P L)
    (labels : List (Label P L)) (hlen : labels.length = G.nodeCount) :
    Fin G.nodeCount → TypedValue L := by
  intro node
  exact
    if hidx : (node : Nat) < labels.length then
      (labels.get ⟨(node : Nat), hidx⟩).toTypedValue
    else
      False.elim (by
        have hnode : (node : Nat) < labels.length := by
          simp [hlen, node.isLt]
        exact hidx hnode)

theorem labelValueAssignment_eq_of_get?
    (G : Graph P L) (labels : List (Label P L))
    (hlen : labels.length = G.nodeCount)
    (node : Fin G.nodeCount) {label : Label P L}
    (hget : labels[(node : Nat)]? = some label) :
    labelValueAssignment G labels hlen node = label.toTypedValue := by
  unfold labelValueAssignment
  have hidx : (node : Nat) < labels.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  rw [dif_pos hidx]
  rw [List.getElem?_eq_getElem hidx] at hget
  exact congrArg Label.toTypedValue (Option.some.inj hget)

theorem canonicalCompletion_getAs_of_label_get?
    (G : Graph P L) (labels : List (Label P L))
    (hlen : labels.length = G.nodeCount)
    (node : Fin G.nodeCount) {label : Label P L}
    (hget : labels[(node : Nat)]? = some label) (ty : L.Ty) :
    Store.getAs
        (Config.canonicalCompletion G
          (labelValueAssignment G labels hlen)).store
        (G.nodeTarget node) ty =
      label.toTypedValue.as? ty := by
  have hmem :
      (node, label.toTypedValue) ∈
        G.nodeOrder.map
          (fun node => (node, labelValueAssignment G labels hlen node)) :=
    List.mem_map.mpr
      ⟨node, G.mem_nodeOrder node, by
        exact Prod.ext rfl
          (labelValueAssignment_eq_of_get? G labels hlen node hget)⟩
  have hread :=
    Config.completeNodes_getAs_of_mem
      (cfg := Config.initial G)
      (steps := G.nodeOrder.map
        (fun node => (node, labelValueAssignment G labels hlen node)))
      (hnodup := by
        rw [Config.map_fst_pair]
        exact G.nodeOrder_nodup)
      (node := node)
      (value := label.toTypedValue)
      hmem ty
  simpa [Config.canonicalCompletion, Config.scheduleComplete] using hread

theorem canonicalCompletion_getAs_of_label_get?_base
    (G : Graph P L) (labels : List (Label P L))
    (hlen : labels.length = G.nodeCount)
    (node : Fin G.nodeCount) {label : Label P L}
    (hget : labels[(node : Nat)]? = some label) :
    Store.getAs
        (Config.canonicalCompletion G
          (labelValueAssignment G labels hlen)).store
        (G.nodeTarget node) label.ty =
      some (cast (by rw [Label.toTypedValue_ty]) label.toTypedValue.value) := by
  rw [canonicalCompletion_getAs_of_label_get? G labels hlen node hget]
  simp [TypedValue.as?]

/-- Open source start configuration for a graph-compilable program. -/
def sourceStart (g : GraphProgram P L) : SourceConfig P L where
  ctx := g.Γ
  env := g.env
  cont := g.prog

/-- Run-level representation up to the concrete terminal store produced by the
lockstep induction. The remaining strengthening is to identify this store with
`canonicalCompletion` for `labelValueAssignment`. -/
theorem sourceEnv_runStore_exists
    (g : GraphProgram P L)
    {labels : List (Label P L)} {final : SourceConfig P L}
    (hrun : SourceConfig.LabeledStar (sourceStart g) labels final)
    (hterminal : final.IsTerminal) :
    let result := buildResult g
    ∃ hctx : final.ctx = result.terminalCtx,
      ∃ terminalStore : Store L,
        ∃ available :
          ∀ {name bindTy}
            (h : VHasVar result.terminalCtx name bindTy),
            ∃ value, Store.getAs terminalStore
              (result.terminalState.fieldOf h) bindTy.base = some value,
          sourceEnvOfStore result.terminalState terminalStore available =
            cast (congrArg (VEnv L) hctx) final.env := by
  let init := initialState g.Γ g.env g.wctx
  let state := BuildState.fromInitial init
  let result := compileCore g.prog g.fresh g.normalized state
  let initialStore : Store L :=
    (({ initialFields := init.initialFields, nodes := result.nodes } :
      Graph P L).initialStore)
  have hagree₀ : StoreAgree state g.env initialStore := by
    intro name bindTy h
    simpa [state, init, initialStore, BuildState.fromInitial] using
      initialState_initialStore_get
        (env := g.env) (wctx := g.wctx) result.nodes h
  have hrun' :
      SourceConfig.LabeledStar
        ({ ctx := g.Γ, env := g.env, cont := g.prog } :
          SourceConfig P L)
        labels final := by
    simpa [sourceStart] using hrun
  rcases
      StoreAgree_run_exists_compileCore
        hrun' g.fresh g.normalized state hagree₀ hterminal with
    ⟨hctx, terminalStore, hagree⟩
  let available :
      ∀ {name bindTy}
        (h : VHasVar result.terminalCtx name bindTy),
        ∃ value, Store.getAs terminalStore
          (result.terminalState.fieldOf h) bindTy.base = some value := by
    intro name bindTy h
    exact ⟨_, hagree h⟩
  refine ⟨hctx, terminalStore, available, ?_⟩
  simpa [result] using
    sourceEnvOfStore_eq_of_storeAgree
      (state := result.terminalState)
      (env := cast (congrArg (VEnv L) hctx) final.env)
      (store := terminalStore)
      hagree
      available

end ToEventGraph

end Vegas
