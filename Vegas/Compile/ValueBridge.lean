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

`Label.toTypedValue` packs a label's value as a graph `TypedValue`.  The main
representation theorem, `sourceEnv_runConfig`, says a terminal source run's own
labelled values, written into the compiled graph's canonical completion, read
back as the run's terminal source environment through `sourceEnvOfStore`.
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

theorem StoreAgree.store_eq
    {Γ : VCtx P L} {state : BuildState P L Γ}
    {env : VEnv L Γ} {store store' : Store L}
    (hagree : StoreAgree state env store) (hstore : store = store') :
    StoreAgree state env store' := by
  intro name bindTy h
  rw [← hstore]
  exact hagree h

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

/-- If a store already contains the field allocated by `addEvent`, agreement
extends without changing the store. This is the preservation principle used
with `canonicalCompletion`, whose store writes all node fields up front. -/
theorem StoreAgree.addEvent_of_getAs
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
    (value : L.Val bindTy.base)
    (hread :
      Store.getAs store state.nextField bindTy.base = some value) :
    StoreAgree
      (state.addEvent name bindTy sem hfresh hnode).1
      (VEnv.cons (x := name) (τ := bindTy) value env)
      store := by
  intro query queryTy h
  cases h with
  | here =>
      simpa [BuildState.addEvent_fieldOf_here] using hread
  | there htail =>
      rw [BuildState.addEvent_fieldOf_there]
      exact hagree htail

/-- `cfg` has completed exactly the graph nodes whose numeric ids are below
`next`. This is the prefix invariant for source-order graph execution. -/
def DonePrefix {G : Graph P L} (cfg : Config G) (next : Nat) : Prop :=
  ∀ node : Fin G.nodeCount, node ∈ cfg.done ↔ (node : Nat) < next

theorem DonePrefix.initial (G : Graph P L) :
    DonePrefix (Config.initial G) 0 := by
  intro node
  simp [Config.initial]

theorem DonePrefix.ready
    {G : Graph P L} {cfg : Config G} {next : Nat}
    (hdone : DonePrefix cfg next)
    {node : Fin G.nodeCount} (hnode : (node : Nat) = next) :
    Ready G cfg node := by
  constructor
  · intro hmem
    have hlt := (hdone node).mp hmem
    omega
  · intro prior hprior
    exact (hdone prior).mpr (by
      have hlt := G.prereq_lt hprior
      omega)

theorem DonePrefix.completeNode
    {G : Graph P L} {cfg : Config G} {next : Nat}
    (hdone : DonePrefix cfg next)
    {node : Fin G.nodeCount} (hnode : (node : Nat) = next)
    (value : TypedValue L) :
    DonePrefix (cfg.completeNode node value) (next + 1) := by
  intro query
  constructor
  · intro hmem
    have hcases : query = node ∨ query ∈ cfg.done := by
      simpa [Config.completeNode] using hmem
    cases hcases with
    | inl heq =>
        rw [heq, hnode]
        omega
    | inr hold =>
        have hlt := (hdone query).mp hold
        omega
  · intro hltSucc
    by_cases hq : query = node
    · simp [Config.completeNode, hq]
    · have hlt : (query : Nat) < next := by
        by_contra hnot
        have hge : next ≤ (query : Nat) := Nat.le_of_not_gt hnot
        have hle : (query : Nat) ≤ next := by omega
        have hval : (query : Nat) = (node : Nat) := by omega
        exact hq (Fin.ext hval)
      have hdoneQuery : query ∈ cfg.done := (hdone query).mpr hlt
      simpa [Config.completeNode, hq] using hdoneQuery

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

/-- The canonical terminal store obtained by writing a complete source label
trace into the graph's canonical node order. -/
noncomputable def canonicalLabelStore (G : Graph P L)
    (labels : List (Label P L)) (hlen : labels.length = G.nodeCount) :
    Store L :=
  (Config.canonicalCompletion G
    (labelValueAssignment G labels hlen)).store

omit [DecidableEq P] in
theorem label_get?_append_cons_length
    (pre rest : List (Label P L)) (label : Label P L) :
    (pre ++ label :: rest)[pre.length]? = some label := by
  induction pre with
  | nil =>
      simp
  | cons _ tail _ih =>
      simp

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

theorem labelValueAssignment_irrel
    (G : Graph P L) (labels : List (Label P L))
    (hlen₁ hlen₂ : labels.length = G.nodeCount) :
    labelValueAssignment G labels hlen₁ =
      labelValueAssignment G labels hlen₂ := by
  funext node
  unfold labelValueAssignment
  by_cases hidx : (node : Nat) < labels.length
  · simp [hidx]
  · have hidx' : (node : Nat) < labels.length := by
      simp [hlen₁, node.isLt]
    exact False.elim (hidx hidx')

theorem canonicalLabelStore_irrel
    (G : Graph P L) (labels : List (Label P L))
    (hlen₁ hlen₂ : labels.length = G.nodeCount) :
    canonicalLabelStore G labels hlen₁ =
      canonicalLabelStore G labels hlen₂ := by
  unfold canonicalLabelStore
  rw [labelValueAssignment_irrel G labels hlen₁ hlen₂]

theorem canonicalCompletion_getAs_of_initial_field
    (G : Graph P L) (labels : List (Label P L))
    (hlen : labels.length = G.nodeCount)
    {field : Nat} {ty : L.Ty}
    (hfield : field < G.initialFields.length) :
    Store.getAs
        (Config.canonicalCompletion G
          (labelValueAssignment G labels hlen)).store
        field ty =
      Store.getAs G.initialStore field ty := by
  have hnot :
      ∀ step,
        step ∈ G.nodeOrder.map
          (fun node => (node, labelValueAssignment G labels hlen node)) →
          field ≠ G.nodeTarget step.1 := by
    intro step _hstep heq
    unfold Graph.nodeTarget at heq
    omega
  have hread :=
    Config.completeNodes_getAs_of_not_targets
      (cfg := Config.initial G)
      (steps := G.nodeOrder.map
        (fun node => (node, labelValueAssignment G labels hlen node)))
      (field := field) (ty := ty) hnot
  simpa [Config.canonicalCompletion, Config.scheduleComplete,
    Config.initial] using hread

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

theorem canonicalLabelStore_getAs_of_prefix_head
    (G : Graph P L) (fullLabels : List (Label P L))
    (hlen : fullLabels.length = G.nodeCount)
    (pre rest : List (Label P L)) (label : Label P L)
    (hfull : fullLabels = pre ++ label :: rest)
    (node : Fin G.nodeCount)
    (hnode : (node : Nat) = pre.length) :
    Store.getAs
        (canonicalLabelStore G fullLabels hlen)
        (G.nodeTarget node) label.ty =
      some (cast (by rw [Label.toTypedValue_ty]) label.toTypedValue.value) := by
  have hget : fullLabels[(node : Nat)]? = some label := by
    rw [hfull, hnode]
    exact label_get?_append_cons_length pre rest label
  simpa [canonicalLabelStore] using
    canonicalCompletion_getAs_of_label_get?_base
      G fullLabels hlen node hget

/-- Generalized representation theorem for a source run: if the source variables
already in `state` agree with the final canonical label store, then after
compiling and running the remaining source suffix, the terminal compiler state
agrees with the terminal source environment in that same canonical store. -/
theorem StoreAgree_run_canonical_compileCore
    {start final : SourceConfig P L}
    {labels fullLabels : List (Label P L)}
    (hrun : SourceConfig.LabeledStar start labels final)
    (fresh : FreshBindings start.cont)
    (normalized : NormalizedDists start.cont)
    (state : BuildState P L start.ctx)
    (pre : List (Label P L))
    (hfull : fullLabels = pre ++ labels)
    (hpre : pre.length = state.nodes.length)
    (hterminal : final.IsTerminal)
    (hlen :
      fullLabels.length =
        (BuildResult.graph
          (compileCore start.cont fresh normalized state)).nodeCount)
    (hagree :
      StoreAgree state start.env
        (canonicalLabelStore
          (BuildResult.graph
            (compileCore start.cont fresh normalized state))
          fullLabels hlen)) :
    let result := compileCore start.cont fresh normalized state
    ∃ hctx : final.ctx = result.terminalCtx,
      StoreAgree result.terminalState
        (cast (congrArg (VEnv L) hctx) final.env)
        (canonicalLabelStore result.graph fullLabels hlen) := by
  induction hrun generalizing pre with
  | refl cfg =>
      rcases cfg with ⟨Γ, env, cont⟩
      dsimp [SourceConfig.IsTerminal] at hterminal
      obtain ⟨payoffs, hpayoffs⟩ := hterminal
      subst cont
      refine ⟨rfl, ?_⟩
      intro name bindTy h
      simpa [compileCore] using hagree h
  | cons step rest ih =>
      rename_i a b c stepLabel tailLabels
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
          let G : Graph P L :=
            BuildResult.graph
              (compileCore (VegasCore.sample x D' k) fresh normalized state)
          have hidx : state.nodes.length < G.nodeCount := by
            have hlt : state.nodes.length < fullLabels.length := by
              rw [hfull, ← hpre]
              simp
            simpa [G, hlen] using hlt
          let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
          have htarget : G.nodeTarget node = state.nextField := by
            simp [G, node, BuildResult.graph, Graph.nodeTarget,
              BuildState.nextField, BuildState.nextNode,
              compileCore_initialFields]
          have hread :
              Store.getAs (canonicalLabelStore G fullLabels hlen)
                state.nextField graphDist.ty = some v := by
            have hreadNode :=
              canonicalLabelStore_getAs_of_prefix_head
                G fullLabels hlen pre tailLabels (Label.sample x v) hfull
                node (by
                  simp only [node]
                  exact hpre.symm)
            simpa [Label.ty, Label.toTypedValue, graphDist, htarget] using
              hreadNode
          have hagreeAdded :
              StoreAgree added.1 (VEnv.cons v env)
                (canonicalLabelStore G fullLabels hlen) := by
            exact
              hagree.addEvent_of_getAs x (.pub graphDist.ty) sem fresh.1
                hnode v hread
          have hfullTail :
              fullLabels =
                (pre ++ [Label.sample x v]) ++ tailLabels := by
            simpa [List.append_assoc] using hfull
          have hpreTail :
              (pre ++ [Label.sample x v]).length = added.1.nodes.length := by
            simp [added, hpre, BuildState.addEvent_nodes]
          have hlenTail :
              fullLabels.length =
                (BuildResult.graph
                  (compileCore k fresh.2 normalized.2 added.1)).nodeCount := by
            simpa [G, compileCore, graphDist, sem, event, hnode, added] using
              hlen
          have hagreeTail :
              StoreAgree added.1 (VEnv.cons v env)
                (canonicalLabelStore
                  (BuildResult.graph
                    (compileCore k fresh.2 normalized.2 added.1))
                  fullLabels hlenTail) := by
            have hstore :
                canonicalLabelStore
                    (BuildResult.graph
                      (compileCore k fresh.2 normalized.2 added.1))
                    fullLabels hlenTail =
                  canonicalLabelStore G fullLabels hlen :=
              canonicalLabelStore_irrel
                (BuildResult.graph
                  (compileCore k fresh.2 normalized.2 added.1))
                fullLabels hlenTail hlen
            intro name bindTy h
            rw [hstore]
            exact hagreeAdded h
          rcases
              ih fresh.2 normalized.2 added.1
                (pre ++ [Label.sample x v])
                hfullTail hpreTail hterminal hlenTail hagreeTail with
            ⟨hctx, hfinalAgree⟩
          refine ⟨hctx, ?_⟩
          have hfinalAgreeCurrent :
              StoreAgree
                (compileCore k fresh.2 normalized.2 added.1).terminalState
                (cast (congrArg (VEnv L) hctx) c.env)
                (canonicalLabelStore G fullLabels hlen) := by
            have hstore :
                canonicalLabelStore
                    (BuildResult.graph
                      (compileCore k fresh.2 normalized.2 added.1))
                    fullLabels hlenTail =
                  canonicalLabelStore G fullLabels hlen :=
              canonicalLabelStore_irrel
                (BuildResult.graph
                  (compileCore k fresh.2 normalized.2 added.1))
                fullLabels hlenTail hlen
            intro name bindTy h
            rw [← hstore]
            exact hfinalAgree h
          change
            StoreAgree
              (compileCore k fresh.2 normalized.2 added.1).terminalState
              (cast (congrArg (VEnv L) hctx) c.env)
              (canonicalLabelStore G fullLabels hlen)
          exact hfinalAgreeCurrent
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
          let G : Graph P L :=
            BuildResult.graph
              (compileCore (VegasCore.commit x who R k) fresh normalized state)
          have hidx : state.nodes.length < G.nodeCount := by
            have hlt : state.nodes.length < fullLabels.length := by
              rw [hfull, ← hpre]
              simp
            simpa [G, hlen] using hlt
          let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
          have htarget : G.nodeTarget node = state.nextField := by
            simp [G, node, BuildResult.graph, Graph.nodeTarget,
              BuildState.nextField, BuildState.nextNode,
              compileCore_initialFields]
          have hread :
              Store.getAs (canonicalLabelStore G fullLabels hlen)
                state.nextField graphGuard.ty = some v := by
            have hreadNode :=
              canonicalLabelStore_getAs_of_prefix_head
                G fullLabels hlen pre tailLabels (Label.commit x who v)
                hfull node (by
                  simp only [node]
                  exact hpre.symm)
            simpa [Label.ty, Label.toTypedValue, graphGuard, htarget] using
              hreadNode
          have hagreeAdded :
              StoreAgree added.1 (VEnv.cons v env)
                (canonicalLabelStore G fullLabels hlen) := by
            exact
              hagree.addEvent_of_getAs x (.sealed who graphGuard.ty) sem
                fresh.1 hnode v hread
          have hfullTail :
              fullLabels =
                (pre ++ [Label.commit x who v]) ++ tailLabels := by
            simpa [List.append_assoc] using hfull
          have hpreTail :
              (pre ++ [Label.commit x who v]).length =
                added.1.nodes.length := by
            simp [added, hpre, BuildState.addEvent_nodes]
          have hlenTail :
              fullLabels.length =
                (BuildResult.graph
                  (compileCore k fresh.2 normalized added.1)).nodeCount := by
            simpa [G, compileCore, graphGuard, sem, event, hnode, added] using
              hlen
          have hagreeTail :
              StoreAgree added.1 (VEnv.cons v env)
                (canonicalLabelStore
                  (BuildResult.graph
                    (compileCore k fresh.2 normalized added.1))
                  fullLabels hlenTail) := by
            have hstore :
                canonicalLabelStore
                    (BuildResult.graph
                      (compileCore k fresh.2 normalized added.1))
                    fullLabels hlenTail =
                  canonicalLabelStore G fullLabels hlen :=
              canonicalLabelStore_irrel
                (BuildResult.graph
                  (compileCore k fresh.2 normalized added.1))
                fullLabels hlenTail hlen
            intro name bindTy h
            rw [hstore]
            exact hagreeAdded h
          rcases
              ih fresh.2 normalized added.1
                (pre ++ [Label.commit x who v])
                hfullTail hpreTail hterminal hlenTail hagreeTail with
            ⟨hctx, hfinalAgree⟩
          refine ⟨hctx, ?_⟩
          have hfinalAgreeCurrent :
              StoreAgree
                (compileCore k fresh.2 normalized added.1).terminalState
                (cast (congrArg (VEnv L) hctx) c.env)
                (canonicalLabelStore G fullLabels hlen) := by
            have hstore :
                canonicalLabelStore
                    (BuildResult.graph
                      (compileCore k fresh.2 normalized added.1))
                    fullLabels hlenTail =
                  canonicalLabelStore G fullLabels hlen :=
              canonicalLabelStore_irrel
                (BuildResult.graph
                  (compileCore k fresh.2 normalized added.1))
                fullLabels hlenTail hlen
            intro name bindTy h
            rw [← hstore]
            exact hfinalAgree h
          change
            StoreAgree
              (compileCore k fresh.2 normalized added.1).terminalState
              (cast (congrArg (VEnv L) hctx) c.env)
              (canonicalLabelStore G fullLabels hlen)
          exact hfinalAgreeCurrent
      | @reveal Γ env y who x b hx k =>
          let sourceField := state.fieldOf hx
          let sem := NodeSem.reveal (Player := P) (L := L) sourceField
          let revealed : L.Val b := VEnv.get env hx
          let event : EventNode P L := { ty := b, owner := none, sem := sem }
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
          let added := state.addEvent y (.pub b) sem fresh.1 hnode
          let G : Graph P L :=
            BuildResult.graph
              (compileCore (VegasCore.reveal y who x hx k) fresh normalized
                state)
          have hidx : state.nodes.length < G.nodeCount := by
            have hlt : state.nodes.length < fullLabels.length := by
              rw [hfull, ← hpre]
              simp
            simpa [G, hlen] using hlt
          let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
          have htarget : G.nodeTarget node = state.nextField := by
            simp [G, node, BuildResult.graph, Graph.nodeTarget,
              BuildState.nextField, BuildState.nextNode,
              compileCore_initialFields]
          have hread :
              Store.getAs (canonicalLabelStore G fullLabels hlen)
                state.nextField b = some revealed := by
            have hreadNode :=
              canonicalLabelStore_getAs_of_prefix_head
                G fullLabels hlen pre tailLabels
                (Label.reveal y who x revealed) hfull node (by
                  simp only [node]
                  exact hpre.symm)
            simpa [Label.ty, Label.toTypedValue, revealed, htarget] using
              hreadNode
          have hagreeAdded :
              StoreAgree added.1 (VEnv.cons revealed env)
                (canonicalLabelStore G fullLabels hlen) := by
            exact
              hagree.addEvent_of_getAs y (.pub b) sem fresh.1 hnode
                revealed hread
          have hfullTail :
              fullLabels =
                (pre ++ [Label.reveal y who x revealed]) ++ tailLabels := by
            simpa [List.append_assoc] using hfull
          have hpreTail :
              (pre ++ [Label.reveal y who x revealed]).length =
                added.1.nodes.length := by
            simp [added, hpre, BuildState.addEvent_nodes]
          have hlenTail :
              fullLabels.length =
                (BuildResult.graph
                  (compileCore k fresh.2 normalized added.1)).nodeCount := by
            simpa [G, compileCore, sourceField, sem, event, hnode, added]
              using hlen
          have hagreeTail :
              StoreAgree added.1 (VEnv.cons revealed env)
                (canonicalLabelStore
                  (BuildResult.graph
                    (compileCore k fresh.2 normalized added.1))
                  fullLabels hlenTail) := by
            have hstore :
                canonicalLabelStore
                    (BuildResult.graph
                      (compileCore k fresh.2 normalized added.1))
                    fullLabels hlenTail =
                  canonicalLabelStore G fullLabels hlen :=
              canonicalLabelStore_irrel
                (BuildResult.graph
                  (compileCore k fresh.2 normalized added.1))
                fullLabels hlenTail hlen
            intro name bindTy h
            rw [hstore]
            exact hagreeAdded h
          rcases
              ih fresh.2 normalized added.1
                (pre ++ [Label.reveal y who x revealed])
                hfullTail hpreTail hterminal hlenTail hagreeTail with
            ⟨hctx, hfinalAgree⟩
          refine ⟨hctx, ?_⟩
          have hfinalAgreeCurrent :
              StoreAgree
                (compileCore k fresh.2 normalized added.1).terminalState
                (cast (congrArg (VEnv L) hctx) c.env)
                (canonicalLabelStore G fullLabels hlen) := by
            have hstore :
                canonicalLabelStore
                    (BuildResult.graph
                      (compileCore k fresh.2 normalized added.1))
                    fullLabels hlenTail =
                  canonicalLabelStore G fullLabels hlen :=
              canonicalLabelStore_irrel
                (BuildResult.graph
                  (compileCore k fresh.2 normalized added.1))
                fullLabels hlenTail hlen
            intro name bindTy h
            rw [← hstore]
            exact hfinalAgree h
          change
            StoreAgree
              (compileCore k fresh.2 normalized added.1).terminalState
              (cast (congrArg (VEnv L) hctx) c.env)
              (canonicalLabelStore G fullLabels hlen)
          exact hfinalAgreeCurrent

/-- Initial source values are still readable after completing all event nodes:
canonical completion writes only node-target fields, never initial fields. -/
theorem StoreAgree_fromInitial_canonicalCompletion
    {Γ : VCtx P L} (env : VEnv L Γ) (wctx : WFCtx Γ)
    (nodes : List (EventNode P L)) (labels : List (Label P L))
    (hlen :
      labels.length =
        ({ initialFields := (initialState Γ env wctx).initialFields,
           nodes := nodes } : Graph P L).nodeCount) :
    StoreAgree
      (BuildState.fromInitial (initialState Γ env wctx))
      env
      (Config.canonicalCompletion
        ({ initialFields := (initialState Γ env wctx).initialFields,
           nodes := nodes } : Graph P L)
        (labelValueAssignment
          ({ initialFields := (initialState Γ env wctx).initialFields,
             nodes := nodes } : Graph P L)
          labels hlen)).store := by
  intro name bindTy h
  let G : Graph P L :=
    { initialFields := (initialState Γ env wctx).initialFields,
      nodes := nodes }
  have hlt :
      (initialState Γ env wctx).fieldOf h < G.initialFields.length := by
    simpa [G] using (initialState Γ env wctx).fieldOf_lt h
  have hframe :
      Store.getAs
          (Config.canonicalCompletion G
            (labelValueAssignment G labels hlen)).store
          ((initialState Γ env wctx).fieldOf h) bindTy.base =
        Store.getAs G.initialStore
          ((initialState Γ env wctx).fieldOf h) bindTy.base := by
    exact canonicalCompletion_getAs_of_initial_field G labels hlen hlt
  change
    Store.getAs
        (Config.canonicalCompletion G
          (labelValueAssignment G labels hlen)).store
        ((initialState Γ env wctx).fieldOf h) bindTy.base =
      some (env.get h)
  rw [hframe]
  simpa [StoreAgree, BuildState.fromInitial, G] using
    initialState_initialStore_get
      (env := env) (wctx := wctx) nodes h

/-- Open source start configuration for a graph-compilable program. -/
def sourceStart (g : GraphProgram P L) : SourceConfig P L where
  ctx := g.Γ
  env := g.env
  cont := g.prog

/-- **Representation.** A terminal source run's own labelled values, injected
into the compiled graph in canonical source/node order, reconstruct the source
run's terminal environment through the compiler dictionary. -/
theorem sourceEnv_runConfig
    (g : GraphProgram P L)
    {labels : List (Label P L)} {final : SourceConfig P L}
    (hrun : SourceConfig.LabeledStar (sourceStart g) labels final)
    (hterminal : final.IsTerminal) :
    let result := buildResult g
    ∃ hlen : labels.length = result.graph.nodeCount,
      ∃ hctx : final.ctx = result.terminalCtx,
        ∃ available :
          ∀ {name bindTy}
            (h : VHasVar result.terminalCtx name bindTy),
            ∃ value,
              Store.getAs
                (canonicalLabelStore result.graph labels hlen)
                (result.terminalState.fieldOf h) bindTy.base =
                  some value,
          sourceEnvOfStore result.terminalState
              (canonicalLabelStore result.graph labels hlen)
              available =
            cast (congrArg (VEnv L) hctx) final.env := by
  let init := initialState g.Γ g.env g.wctx
  let state := BuildState.fromInitial init
  let result := compileCore g.prog g.fresh g.normalized state
  have hrun' :
      SourceConfig.LabeledStar
        ({ ctx := g.Γ, env := g.env, cont := g.prog } :
          SourceConfig P L)
        labels final := by
    simpa [sourceStart] using hrun
  have hlabelLen : labels.length = g.prog.instrCount :=
    hrun'.length_eq_instrCount_of_terminal hterminal
  have hlen :
      labels.length =
        (BuildResult.graph result).nodeCount := by
    rw [hlabelLen]
    dsimp [result, BuildResult.graph, Graph.nodeCount]
    rw [compileCore_nodes_length]
    simp [state, init, BuildState.fromInitial_nodes]
  have hlenInitial :
      labels.length =
        ({ initialFields := init.initialFields,
           nodes := result.nodes } : Graph P L).nodeCount := by
    simpa [result, BuildResult.graph, Graph.nodeCount,
      compileCore_initialFields] using hlen
  have hagree₀ :
      StoreAgree state g.env
        (canonicalLabelStore (BuildResult.graph result) labels hlen) := by
    intro name bindTy h
    have hlt :
        state.fieldOf h < (BuildResult.graph result).initialFields.length := by
      simpa [state, init, result, BuildResult.graph,
        compileCore_initialFields] using init.fieldOf_lt h
    have hframe :=
      canonicalCompletion_getAs_of_initial_field
        (BuildResult.graph result) labels hlen
        (field := state.fieldOf h) (ty := bindTy.base) hlt
    have hinitRead :
        Store.getAs (BuildResult.graph result).initialStore
          (state.fieldOf h) bindTy.base = some (g.env.get h) := by
      simpa [state, init, result, BuildResult.graph,
        compileCore_initialFields] using
        initialState_initialStore_get
          (env := g.env) (wctx := g.wctx) result.nodes h
    change
      Store.getAs
          (Config.canonicalCompletion (BuildResult.graph result)
            (labelValueAssignment (BuildResult.graph result) labels hlen)).store
          (state.fieldOf h) bindTy.base =
        some (g.env.get h)
    rw [hframe]
    exact hinitRead
  rcases
      StoreAgree_run_canonical_compileCore
        hrun' g.fresh g.normalized state [] (by simp)
        (by simp [state, init, BuildState.fromInitial_nodes])
        hterminal hlen hagree₀ with
    ⟨hctx, hagree⟩
  let available :
      ∀ {name bindTy}
        (h : VHasVar result.terminalCtx name bindTy),
        ∃ value,
          Store.getAs
            (canonicalLabelStore (BuildResult.graph result) labels hlen)
            (result.terminalState.fieldOf h) bindTy.base = some value := by
    intro name bindTy h
    exact ⟨_, hagree h⟩
  refine ⟨hlen, hctx, available, ?_⟩
  simpa [result] using
    sourceEnvOfStore_eq_of_storeAgree
      (state := result.terminalState)
      (env := cast (congrArg (VEnv L) hctx) final.env)
      (store := canonicalLabelStore (BuildResult.graph result) labels hlen)
      hagree
      available

/-- Run-level representation for the concrete terminal store produced by the
lockstep induction. This existential form is useful when a caller does not need
to expose the canonical graph completion. -/
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
