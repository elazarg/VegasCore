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

/-- R1 readback ingredient for reverse replay: every completed node in a
reachable terminal graph has a typed value at its canonical target field. -/
theorem reachableTerminal_nodeTarget_getAs
    {G : Graph P L} (hwf : G.WF)
    (state : ReachableConfig G)
    (hterminal : Terminal G state.1)
    (node : Fin G.nodeCount) :
    ∃ value : L.Val (G.nodeRow node).ty,
      Store.getAs state.1.store (G.nodeTarget node)
        (G.nodeRow node).ty = some value := by
  have hcoherent : StoreCoherent G state.1 :=
    reachable_storeCoherent hwf state.2
  have hfield :
      G.field? (G.nodeTarget node) =
        some
          { ty := (G.nodeRow node).ty
            owner := (G.nodeRow node).owner
            source := .event (node : Nat) } := by
    exact G.field?_nodeTarget (G.nodes_get?_nodeRow node)
  have hdone : state.1.nodeDone (node : Nat) := by
    change (node : Nat) ∈ state.1.doneIds
    exact Finset.mem_image.mpr ⟨node, hterminal node, rfl⟩
  rcases
      hcoherent (G.nodeTarget node)
        { ty := (G.nodeRow node).ty
          owner := (G.nodeRow node).owner
          source := .event (node : Nat) }
        hfield hdone with
    ⟨value, hvalue⟩
  exact ⟨value, hvalue⟩

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

theorem compileCore_added_head_get?
    {Γ : VCtx P L} {name : VarId} {bindTy : BindTy P L}
    {sem : NodeSem P L}
    (state : BuildState P L Γ)
    (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
          [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt
        state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem })
    (tail : VegasCore P L ((name, bindTy) :: Γ))
    (fresh : FreshBindings tail)
    (normalized : NormalizedDists tail) :
    let added := state.addEvent name bindTy sem hfresh hnode
    (compileCore tail fresh normalized added.1).nodes[state.nodes.length]? =
      some { ty := bindTy.base, owner := bindTy.owner, sem := sem } := by
  intro added
  have hpref := compileCore_nodes_prefix tail fresh normalized added.1
  have hprefEq := List.prefix_iff_eq_append.mp hpref
  have hidxAdded : state.nodes.length < added.1.nodes.length := by
    simp [added, BuildState.addEvent_nodes]
  have hgetAdded :
      added.1.nodes[state.nodes.length]? =
        some { ty := bindTy.base, owner := bindTy.owner, sem := sem } := by
    simp [added, BuildState.addEvent_nodes]
  rw [← hprefEq]
  rw [List.getElem?_append_left hidxAdded]
  exact hgetAdded

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

/-- Forward generation spine: executing the source run in source order yields a
reachable graph configuration over the same compiled graph, with the terminal
compiler dictionary agreeing with the terminal source environment. -/
theorem StoreAgree_run_reachable_compileCore
    {start final : SourceConfig P L} {labels : List (Label P L)}
    (hrun : SourceConfig.LabeledStar start labels final)
    (fresh : FreshBindings start.cont)
    (normalized : NormalizedDists start.cont)
    (state : BuildState P L start.ctx)
    (cfg :
      Config (BuildResult.graph
        (compileCore start.cont fresh normalized state)))
    (hdone : DonePrefix cfg state.nodes.length)
    (hreach :
      Reachable
        (BuildResult.graph
          (compileCore start.cont fresh normalized state))
        cfg)
    (hagree : StoreAgree state start.env cfg.store)
    (hterminal : final.IsTerminal) :
    let result := compileCore start.cont fresh normalized state
    ∃ hctx : final.ctx = result.terminalCtx,
      ∃ terminalCfg : Config result.graph,
        Reachable result.graph terminalCfg ∧
        Terminal result.graph terminalCfg ∧
        StoreAgree result.terminalState
          (cast (congrArg (VEnv L) hctx) final.env)
          terminalCfg.store := by
  induction hrun with
  | refl cfgSrc =>
      rcases cfgSrc with ⟨Γ, env, cont⟩
      dsimp [SourceConfig.IsTerminal] at hterminal
      obtain ⟨payoffs, hpayoffs⟩ := hterminal
      subst cont
      refine ⟨rfl, cfg, ?_, ?_, ?_⟩
      · simpa [compileCore] using hreach
      · intro node
        exact (hdone node).mpr (by
          simp [compileCore, BuildResult.graph, Graph.nodeCount])
      · intro name bindTy h
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
            have hlenNodes :=
              compileCore_nodes_length
                (VegasCore.sample x D' k) fresh normalized state
            change state.nodes.length <
              (compileCore (VegasCore.sample x D' k) fresh normalized state).nodes.length
            rw [hlenNodes]
            simp [VegasCore.instrCount]
          let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
          have hnodeVal : (node : Nat) = state.nodes.length := rfl
          have htarget : G.nodeTarget node = state.nextField := by
            simp [G, node, BuildResult.graph, Graph.nodeTarget,
              BuildState.nextField, BuildState.nextNode,
              compileCore_initialFields]
          have hrow :
              G.nodes[(node : Nat)]? = some event := by
            change
              (compileCore (VegasCore.sample x D' k) fresh normalized
                state).nodes[state.nodes.length]? = some event
            simpa [compileCore, graphDist, sem, event, hnode, added] using
              compileCore_added_head_get?
                (state := state) (name := x) (bindTy := .pub graphDist.ty)
                (sem := sem) (hfresh := fresh.1) (hnode := hnode)
                k fresh.2 normalized.2
          have hready : Ready G cfg node :=
            hdone.ready hnodeVal
          let available :
              ∀ {name bindTy} (h : VHasVar Γ name bindTy),
                ∃ value, Store.getAs cfg.store (state.fieldOf h)
                  bindTy.base = some value := by
            intro name bindTy h
            exact ⟨_, hagree h⟩
          rcases
              eventDistOf_readEnv_agrees_sourceEnvOfStore
                state D' normalized.1 cfg.store available with
            ⟨readEnv, hreadEnv, hreadAgrees⟩
          have hsourceEnv :
              sourceEnvOfStore state cfg.store available = env :=
            sourceEnvOfStore_eq_of_storeAgree hagree available
          have hdistEval :=
            eventDistOf_eval_eq_eval
              state D' normalized.1 (VEnv.erasePubEnv env) readEnv
              (by
                intro name depTy hvar hmem
                simpa [hsourceEnv] using hreadAgrees hvar hmem)
          rcases hdistEval with ⟨hnormalized, hdistEval⟩
          have hsupport :
              v ∈ (graphDist.eval readEnv).support := by
            have hsupport' :
                v ∈
                  ((eventDistOf state D' normalized.1).eval readEnv).support := by
              rw [hdistEval]
              exact
                (FWeight.mem_support_toPMF
                  (L.evalDist D' (VEnv.erasePubEnv env)) hnormalized v).mpr (by
                simpa [VEnv.eraseSampleEnv] using hv)
            simpa [graphDist] using hsupport'
          let internal : InternalEvent G := { node := node }
          let internalStep : InternalStep G cfg internal :=
            .sample event graphDist hrow rfl hready readEnv hreadEnv
          let availableEvent : AvailableEvent G cfg :=
            .internal internal internalStep
          let written : TypedValue L := { ty := graphDist.ty, value := v }
          let nextCfg : Config G := cfg.completeNode node written
          have hnext :
              nextCfg ∈ (stepAvailableEvent G cfg availableEvent).support := by
            dsimp [availableEvent, internalStep, nextCfg, stepAvailableEvent,
              stepInternal, written]
            exact (PMF.mem_support_map_iff _ _ _).mpr
              ⟨v, hsupport, rfl⟩
          have hreachNext : Reachable G nextCfg :=
            Reachable.step hreach availableEvent hnext
          have hdoneNext : DonePrefix nextCfg added.1.nodes.length := by
            have hdoneStep :=
              hdone.completeNode (node := node) hnodeVal written
            simpa [nextCfg, added, BuildState.addEvent_nodes] using hdoneStep
          have hagreeNext : StoreAgree added.1 (VEnv.cons v env) nextCfg.store := by
            have hraw :
                StoreAgree added.1 (VEnv.cons v env)
                  (Store.set cfg.store state.nextField written) := by
              intro name bindTy h
              simpa [written, added] using
                (hagree.addEvent x (.pub graphDist.ty) sem fresh.1 hnode v) h
            change
              StoreAgree added.1 (VEnv.cons v env)
                (Store.set cfg.store (G.nodeTarget node) written)
            rw [htarget]
            exact hraw
          let hcfgCast :
              Config (BuildResult.graph
                (compileCore k fresh.2 normalized.2 added.1)) := by
            simpa [G, compileCore, graphDist, sem, event, hnode, added] using
              nextCfg
          have hdoneCast :
              DonePrefix hcfgCast added.1.nodes.length := by
            change DonePrefix nextCfg added.1.nodes.length
            exact hdoneNext
          have hreachCast :
              Reachable
                (BuildResult.graph
                  (compileCore k fresh.2 normalized.2 added.1))
                hcfgCast := by
            change Reachable G nextCfg
            exact hreachNext
          have hagreeCast : StoreAgree added.1 (VEnv.cons v env) hcfgCast.store := by
            change StoreAgree added.1 (VEnv.cons v env) nextCfg.store
            exact hagreeNext
          rcases
              ih fresh.2 normalized.2 added.1 hcfgCast
                hdoneCast hreachCast hagreeCast hterminal with
            ⟨hctx, terminalCfg, hreachTerminal, hterminalGraph, hagreeTerminal⟩
          refine ⟨hctx, terminalCfg, ?_, hterminalGraph, hagreeTerminal⟩
          simpa [G, compileCore, graphDist, sem, event, hnode, added] using
            hreachTerminal
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
            have hlenNodes :=
              compileCore_nodes_length
                (VegasCore.commit x who R k) fresh normalized state
            change state.nodes.length <
              (compileCore (VegasCore.commit x who R k) fresh normalized state).nodes.length
            rw [hlenNodes]
            simp [VegasCore.instrCount]
          let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
          have hnodeVal : (node : Nat) = state.nodes.length := rfl
          have htarget : G.nodeTarget node = state.nextField := by
            simp [G, node, BuildResult.graph, Graph.nodeTarget,
              BuildState.nextField, BuildState.nextNode,
              compileCore_initialFields]
          have hrow : G.nodes[(node : Nat)]? = some event := by
            change
              (compileCore (VegasCore.commit x who R k) fresh normalized
                state).nodes[state.nodes.length]? = some event
            simpa [compileCore, graphGuard, sem, event, hnode, added] using
              compileCore_added_head_get?
                (state := state) (name := x)
                (bindTy := .sealed who graphGuard.ty) (sem := sem)
                (hfresh := fresh.1) (hnode := hnode)
                k fresh.2 normalized
          have hready : Ready G cfg node :=
            hdone.ready hnodeVal
          let available :
              ∀ {name bindTy} (h : VHasVar Γ name bindTy),
                ∃ value, Store.getAs cfg.store (state.fieldOf h)
                  bindTy.base = some value := by
            intro name bindTy h
            exact ⟨_, hagree h⟩
          rcases
              eventGuardOf_readEnv_of_sourceStoreAvailable
                state who R cfg.store available with
            ⟨readEnv, hreadEnv⟩
          have hsourceEnv :
              sourceEnvOfStore state cfg.store available = env :=
            sourceEnvOfStore_eq_of_storeAgree hagree available
          have hviewEq :=
            viewEnvOfReadEnv_eq_eraseEnv_sourceEnvOfStore
              state who cfg.store available readEnv hreadEnv
          have hguardGraph : graphGuard.eval v readEnv = true := by
            change (eventGuardOf state who R).eval v readEnv = true
            rw [eventGuardOf_eval_eq_eval, hviewEq, hsourceEnv]
            exact hguard
          let written : TypedValue L := { ty := graphGuard.ty, value := v }
          let action : CommitAction G who := { node := node, value := written }
          have hvalueOk : action.value.as? graphGuard.ty = some v := by
            simp [action, written, TypedValue.as?]
            rfl
          let commitStep : CommitStep G cfg who action :=
            { row := event
              guard := graphGuard
              row_get := hrow
              sem_eq := rfl
              ready := hready
              value := v
              value_ok := hvalueOk
              env := readEnv
              env_ok := hreadEnv
              guard_ok := hguardGraph }
          let availableEvent : AvailableEvent G cfg :=
            .commit who action commitStep
          let nextCfg : Config G := cfg.completeNode node written
          have hnext :
              nextCfg ∈ (stepAvailableEvent G cfg availableEvent).support := by
            dsimp [availableEvent, commitStep, nextCfg, stepAvailableEvent,
              stepCommit, written]
            rw [PMF.support_pure, Set.mem_singleton_iff]
          have hreachNext : Reachable G nextCfg :=
            Reachable.step hreach availableEvent hnext
          have hdoneNext : DonePrefix nextCfg added.1.nodes.length := by
            have hdoneStep :=
              hdone.completeNode (node := node) hnodeVal written
            simpa [nextCfg, added, BuildState.addEvent_nodes] using hdoneStep
          have hagreeNext : StoreAgree added.1 (VEnv.cons v env) nextCfg.store := by
            have hraw :
                StoreAgree added.1 (VEnv.cons v env)
                  (Store.set cfg.store state.nextField written) := by
              intro name bindTy h
              simpa [written, added] using
                (hagree.addEvent x (.sealed who graphGuard.ty) sem fresh.1
                  hnode v) h
            change
              StoreAgree added.1 (VEnv.cons v env)
                (Store.set cfg.store (G.nodeTarget node) written)
            rw [htarget]
            exact hraw
          let hcfgCast :
              Config (BuildResult.graph
                (compileCore k fresh.2 normalized added.1)) := by
            simpa [G, compileCore, graphGuard, sem, event, hnode, added] using
              nextCfg
          have hdoneCast :
              DonePrefix hcfgCast added.1.nodes.length := by
            change DonePrefix nextCfg added.1.nodes.length
            exact hdoneNext
          have hreachCast :
              Reachable
                (BuildResult.graph
                  (compileCore k fresh.2 normalized added.1))
                hcfgCast := by
            change Reachable G nextCfg
            exact hreachNext
          have hagreeCast :
              StoreAgree added.1 (VEnv.cons v env) hcfgCast.store := by
            change StoreAgree added.1 (VEnv.cons v env) nextCfg.store
            exact hagreeNext
          rcases
              ih fresh.2 normalized added.1 hcfgCast
                hdoneCast hreachCast hagreeCast hterminal with
            ⟨hctx, terminalCfg, hreachTerminal, hterminalGraph, hagreeTerminal⟩
          refine ⟨hctx, terminalCfg, ?_, hterminalGraph, hagreeTerminal⟩
          simpa [G, compileCore, graphGuard, sem, event, hnode, added] using
            hreachTerminal
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
            have hlenNodes :=
              compileCore_nodes_length
                (VegasCore.reveal y who x hx k) fresh normalized state
            change state.nodes.length <
              (compileCore (VegasCore.reveal y who x hx k) fresh normalized
                state).nodes.length
            rw [hlenNodes]
            simp [VegasCore.instrCount]
          let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
          have hnodeVal : (node : Nat) = state.nodes.length := rfl
          have htarget : G.nodeTarget node = state.nextField := by
            simp [G, node, BuildResult.graph, Graph.nodeTarget,
              BuildState.nextField, BuildState.nextNode,
              compileCore_initialFields]
          have hrow : G.nodes[(node : Nat)]? = some event := by
            change
              (compileCore (VegasCore.reveal y who x hx k) fresh normalized
                state).nodes[state.nodes.length]? = some event
            simpa [compileCore, sourceField, sem, event, hnode, added] using
              compileCore_added_head_get?
                (state := state) (name := y) (bindTy := .pub b)
                (sem := sem) (hfresh := fresh.1) (hnode := hnode)
                k fresh.2 normalized
          have hready : Ready G cfg node :=
            hdone.ready hnodeVal
          have hsourceValue :
              Store.getAs cfg.store sourceField b = some revealed := by
            simpa [sourceField, revealed] using hagree hx
          let internal : InternalEvent G := { node := node }
          let internalStep : InternalStep G cfg internal :=
            .reveal event sourceField hrow rfl hready revealed hsourceValue
          let availableEvent : AvailableEvent G cfg :=
            .internal internal internalStep
          let written : TypedValue L := { ty := b, value := revealed }
          let nextCfg : Config G := cfg.completeNode node written
          have hnext :
              nextCfg ∈ (stepAvailableEvent G cfg availableEvent).support := by
            dsimp [availableEvent, internalStep, nextCfg, stepAvailableEvent,
              stepInternal, written]
            rw [PMF.support_pure, Set.mem_singleton_iff]
          have hreachNext : Reachable G nextCfg :=
            Reachable.step hreach availableEvent hnext
          have hdoneNext : DonePrefix nextCfg added.1.nodes.length := by
            have hdoneStep :=
              hdone.completeNode (node := node) hnodeVal written
            simpa [nextCfg, added, BuildState.addEvent_nodes] using hdoneStep
          have hagreeNext :
              StoreAgree added.1 (VEnv.cons revealed env) nextCfg.store := by
            have hraw :
                StoreAgree added.1 (VEnv.cons revealed env)
                  (Store.set cfg.store state.nextField written) := by
              intro name bindTy h
              simpa [written, added] using
                (hagree.addEvent y (.pub b) sem fresh.1 hnode revealed) h
            change
              StoreAgree added.1 (VEnv.cons revealed env)
                (Store.set cfg.store (G.nodeTarget node) written)
            rw [htarget]
            exact hraw
          let hcfgCast :
              Config (BuildResult.graph
                (compileCore k fresh.2 normalized added.1)) := by
            simpa [G, compileCore, sourceField, sem, event, hnode, added] using
              nextCfg
          have hdoneCast :
              DonePrefix hcfgCast added.1.nodes.length := by
            change DonePrefix nextCfg added.1.nodes.length
            exact hdoneNext
          have hreachCast :
              Reachable
                (BuildResult.graph
                  (compileCore k fresh.2 normalized added.1))
                hcfgCast := by
            change Reachable G nextCfg
            exact hreachNext
          have hagreeCast :
              StoreAgree added.1 (VEnv.cons revealed env) hcfgCast.store := by
            change StoreAgree added.1 (VEnv.cons revealed env) nextCfg.store
            exact hagreeNext
          rcases
              ih fresh.2 normalized added.1 hcfgCast
                hdoneCast hreachCast hagreeCast hterminal with
            ⟨hctx, terminalCfg, hreachTerminal, hterminalGraph, hagreeTerminal⟩
          refine ⟨hctx, terminalCfg, ?_, hterminalGraph, hagreeTerminal⟩
          simpa [G, compileCore, sourceField, sem, event, hnode, added] using
            hreachTerminal

/-- Reverse replay spine: a reachable terminal graph store determines a
source-order labelled run whose terminal source environment agrees with the
same store through the compiler dictionary. -/
theorem sourceReplay_compileCore :
    {Γ : VCtx P L} → (env : VEnv L Γ) →
      (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) →
      (normalized : NormalizedDists prog) →
      (state : BuildState P L Γ) →
      (cfg :
        ReachableConfig
          (BuildResult.graph
            (compileCore prog fresh normalized state))) →
      Terminal
        (BuildResult.graph
          (compileCore prog fresh normalized state))
        cfg.1 →
      StoreAgree state env cfg.1.store →
      let result := compileCore prog fresh normalized state
      ∃ labels : List (Label P L),
        ∃ final : SourceConfig P L,
          SourceConfig.LabeledStar
            ({ ctx := Γ, env := env, cont := prog } : SourceConfig P L)
            labels final ∧
          final.IsTerminal ∧
          ∃ hctx : final.ctx = result.terminalCtx,
            StoreAgree result.terminalState
              (cast (congrArg (VEnv L) hctx) final.env)
              cfg.1.store
  | Γ, env, .ret payoffs, fresh, normalized, state, cfg, hterminal,
      hagree => by
      refine ⟨[], ⟨Γ, env, .ret payoffs⟩, ?_, ?_, ?_⟩
      · exact SourceConfig.LabeledStar.refl _
      · exact ⟨payoffs, rfl⟩
      · refine ⟨rfl, ?_⟩
        intro name bindTy h
        simpa [compileCore] using hagree h
  | Γ, env, .sample (b := b) x D' k, fresh, normalized, state, cfg, hterminal,
      hagree => by
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
      let added := state.addEvent x (.pub graphDist.ty) sem fresh.1 hnode
      let result :=
        compileCore (VegasCore.sample x D' k) fresh normalized state
      let G : Graph P L := BuildResult.graph result
      have hidx : state.nodes.length < G.nodeCount := by
        have hlenNodes :=
          compileCore_nodes_length
            (VegasCore.sample x D' k) fresh normalized state
        change state.nodes.length <
          (compileCore (VegasCore.sample x D' k) fresh normalized
            state).nodes.length
        rw [hlenNodes]
        simp [VegasCore.instrCount]
      let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
      have htarget : G.nodeTarget node = state.nextField := by
        simp [G, result, node, BuildResult.graph, Graph.nodeTarget,
          BuildState.nextField, BuildState.nextNode,
          compileCore_initialFields]
      have hrow :
          G.nodes[(node : Nat)]? = some event := by
        change
          (compileCore (VegasCore.sample x D' k) fresh normalized
            state).nodes[state.nodes.length]? = some event
        simpa [compileCore, graphDist, sem, event, hnode, added] using
          compileCore_added_head_get?
            (state := state) (name := x) (bindTy := .pub graphDist.ty)
            (sem := sem) (hfresh := fresh.1) (hnode := hnode)
            k fresh.2 normalized.2
      have hvalidDone : ValidDoneValues G cfg.1 := by
        simpa [G, result] using
          reachable_validDoneValues
            (compileCore (VegasCore.sample x D' k) fresh normalized
              state).graphWF
            cfg.2
      rcases hvalidDone node (hterminal node) with
        ⟨row, hrowValid, hvalid⟩
      have hrowEq : row = event :=
        Option.some.inj (hrowValid.symm.trans hrow)
      subst row
      change
        (match event.sem with
        | .sample dist =>
            ∃ value : L.Val dist.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) dist.ty =
                some value ∧
              ∃ readEnv : ReadEnv L dist.reads,
                ReadEnv.ofStore? cfg.1.store dist.reads = some readEnv ∧
                value ∈ (dist.eval readEnv).support
        | .commit _ guard =>
            ∃ value : L.Val guard.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) guard.ty =
                some value ∧
              ∃ readEnv : ReadEnv L guard.choiceReads,
                ReadEnv.ofStore? cfg.1.store guard.choiceReads =
                  some readEnv ∧
                guard.eval value readEnv = true
        | .reveal source =>
            ∃ value : L.Val event.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) event.ty =
                some value ∧
              Store.getAs cfg.1.store source event.ty = some value) at hvalid
      dsimp [event, sem, graphDist, eventDistOf] at hvalid
      rcases hvalid with ⟨value, htargetValue, readEnv, hreadEnv, hsupport⟩
      let available :
          ∀ {name bindTy} (h : VHasVar Γ name bindTy),
            ∃ value, Store.getAs cfg.1.store (state.fieldOf h)
              bindTy.base = some value := by
        intro name bindTy h
        exact ⟨_, hagree h⟩
      have hsourceEnv :
          sourceEnvOfStore state cfg.1.store available = env :=
        sourceEnvOfStore_eq_of_storeAgree hagree available
      have hagrees :
          ∀ {name depTy}
            (hvar : HasVar (erasePubVCtx Γ) name depTy)
            (hmem : name ∈ L.distDeps D'),
            sourceValuePub state readEnv hvar
              (distReadRefs_mem state D' hvar hmem) =
              VEnv.erasePubEnv
                (sourceEnvOfStore state cfg.1.store available)
                name depTy hvar :=
        eventDistOf_readEnv_agrees_sourceEnvOfStore_of_readEnv
          state D' normalized.1 cfg.1.store available readEnv hreadEnv
      rcases
          eventDistOf_eval_eq_eval
            state D' normalized.1 (VEnv.erasePubEnv env) readEnv
            (by
              intro name depTy hvar hmem
              simpa [hsourceEnv] using hagrees hvar hmem) with
        ⟨hnormalized, hdistEval⟩
      have hsupportSource :
          value ∈ (L.evalDist D' (VEnv.erasePubEnv env)).support := by
        have hsupportPMF :
            value ∈
              ((L.evalDist D' (VEnv.erasePubEnv env)).toPMF
                hnormalized).support := by
          simpa [graphDist] using hdistEval ▸ hsupport
        exact
          (FWeight.mem_support_toPMF
            (L.evalDist D' (VEnv.erasePubEnv env)) hnormalized value).mp
            hsupportPMF
      have hstep :
          LStep
            ({ ctx := Γ, env := env,
               cont := VegasCore.sample x D' k } : SourceConfig P L)
            (.sample x value)
            { ctx := (x, .pub b) :: Γ,
              env := VEnv.cons (x := x) (τ := .pub b) value env,
              cont := k } := by
        simpa [graphDist, VEnv.eraseSampleEnv] using
          LStep.sample D' k value hsupportSource
      have hreadNext :
          Store.getAs cfg.1.store state.nextField graphDist.ty =
            some value := by
        simpa [htarget] using htargetValue
      have hagreeAdded :
          StoreAgree added.1
            (VEnv.cons (x := x) (τ := .pub graphDist.ty) value env)
            cfg.1.store :=
        hagree.addEvent_of_getAs x (.pub graphDist.ty) sem fresh.1 hnode
          value hreadNext
      let tailState : BuildState P L ((x, .pub b) :: Γ) := by
        simpa [graphDist, eventDistOf] using added.1
      let cfgTail :
          ReachableConfig
            (BuildResult.graph
              (compileCore k fresh.2 normalized.2 tailState)) := by
        simpa [tailState, G, result, compileCore, graphDist, eventDistOf,
          sem, event, hnode,
          added] using cfg
      have hterminalTail :
          Terminal
            (BuildResult.graph
              (compileCore k fresh.2 normalized.2 tailState))
            cfgTail.1 := by
        simpa [cfgTail, tailState, G, result, compileCore, graphDist,
          eventDistOf, sem, event, hnode, added] using hterminal
      have hagreeTail :
          StoreAgree tailState
            (VEnv.cons (x := x) (τ := .pub b) value env)
            cfgTail.1.store := by
        intro name bindTy h
        simpa [tailState, cfgTail, graphDist, eventDistOf] using
          hagreeAdded h
      rcases
          sourceReplay_compileCore
            (VEnv.cons (x := x) (τ := .pub b) value env) k
            fresh.2 normalized.2 tailState cfgTail hterminalTail
            hagreeTail with
        ⟨labels, final, htail, hfinalTerminal, hctx, hagreeFinal⟩
      refine ⟨.sample x value :: labels, final, ?_, hfinalTerminal, ?_⟩
      · exact SourceConfig.LabeledStar.cons hstep htail
      · refine ⟨hctx, ?_⟩
        intro name bindTy h
        simpa [cfgTail, tailState, G, result, compileCore, graphDist,
          eventDistOf, sem, event, hnode, added] using
          hagreeFinal h
  | Γ, env, .commit (b := b) x who R k, fresh, normalized, state, cfg, hterminal,
      hagree => by
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
      let result :=
        compileCore (VegasCore.commit x who R k) fresh normalized state
      let G : Graph P L := BuildResult.graph result
      have hidx : state.nodes.length < G.nodeCount := by
        have hlenNodes :=
          compileCore_nodes_length
            (VegasCore.commit x who R k) fresh normalized state
        change state.nodes.length <
          (compileCore (VegasCore.commit x who R k) fresh normalized
            state).nodes.length
        rw [hlenNodes]
        simp [VegasCore.instrCount]
      let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
      have htarget : G.nodeTarget node = state.nextField := by
        simp [G, result, node, BuildResult.graph, Graph.nodeTarget,
          BuildState.nextField, BuildState.nextNode,
          compileCore_initialFields]
      have hrow :
          G.nodes[(node : Nat)]? = some event := by
        change
          (compileCore (VegasCore.commit x who R k) fresh normalized
            state).nodes[state.nodes.length]? = some event
        simpa [compileCore, graphGuard, sem, event, hnode, added] using
          compileCore_added_head_get?
            (state := state) (name := x)
            (bindTy := .sealed who graphGuard.ty) (sem := sem)
            (hfresh := fresh.1) (hnode := hnode)
            k fresh.2 normalized
      have hvalidDone : ValidDoneValues G cfg.1 := by
        simpa [G, result] using
          reachable_validDoneValues
            (compileCore (VegasCore.commit x who R k) fresh normalized
              state).graphWF
            cfg.2
      rcases hvalidDone node (hterminal node) with
        ⟨row, hrowValid, hvalid⟩
      have hrowEq : row = event :=
        Option.some.inj (hrowValid.symm.trans hrow)
      subst row
      change
        (match event.sem with
        | .sample dist =>
            ∃ value : L.Val dist.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) dist.ty =
                some value ∧
              ∃ readEnv : ReadEnv L dist.reads,
                ReadEnv.ofStore? cfg.1.store dist.reads = some readEnv ∧
                value ∈ (dist.eval readEnv).support
        | .commit _ guard =>
            ∃ value : L.Val guard.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) guard.ty =
                some value ∧
              ∃ readEnv : ReadEnv L guard.choiceReads,
                ReadEnv.ofStore? cfg.1.store guard.choiceReads =
                  some readEnv ∧
                guard.eval value readEnv = true
        | .reveal source =>
            ∃ value : L.Val event.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) event.ty =
                some value ∧
              Store.getAs cfg.1.store source event.ty = some value) at hvalid
      dsimp [event, sem, graphGuard, eventGuardOf] at hvalid
      rcases hvalid with ⟨value, htargetValue, readEnv, hreadEnv, hguardGraph⟩
      let available :
          ∀ {name bindTy} (h : VHasVar Γ name bindTy),
            ∃ value, Store.getAs cfg.1.store (state.fieldOf h)
              bindTy.base = some value := by
        intro name bindTy h
        exact ⟨_, hagree h⟩
      have hsourceEnv :
          sourceEnvOfStore state cfg.1.store available = env :=
        sourceEnvOfStore_eq_of_storeAgree hagree available
      have hviewEq :=
        viewEnvOfReadEnv_eq_eraseEnv_sourceEnvOfStore
          state who cfg.1.store available readEnv hreadEnv
      have hguardSource :
          evalGuard (Player := P) (L := L) R value
            (VEnv.eraseEnv (VEnv.toView who env)) = true := by
        change (eventGuardOf state who R).eval value readEnv = true
          at hguardGraph
        rw [eventGuardOf_eval_eq_eval, hviewEq, hsourceEnv] at hguardGraph
        exact hguardGraph
      have hstep :
          LStep
            ({ ctx := Γ, env := env,
               cont := VegasCore.commit x who R k } : SourceConfig P L)
            (.commit x who value)
            { ctx := (x, .sealed who b) :: Γ,
              env := VEnv.cons (x := x) (τ := .sealed who b) value env,
              cont := k } := by
        simpa [graphGuard] using
          LStep.commit R k value hguardSource
      have hreadNext :
          Store.getAs cfg.1.store state.nextField graphGuard.ty =
            some value := by
        simpa [htarget] using htargetValue
      have hagreeAdded :
          StoreAgree added.1
            (VEnv.cons (x := x) (τ := .sealed who graphGuard.ty) value env)
            cfg.1.store :=
        hagree.addEvent_of_getAs x (.sealed who graphGuard.ty) sem fresh.1
          hnode value hreadNext
      let tailState : BuildState P L ((x, .sealed who b) :: Γ) := by
        simpa [graphGuard, eventGuardOf] using added.1
      let cfgTail :
          ReachableConfig
            (BuildResult.graph
              (compileCore k fresh.2 normalized tailState)) := by
        simpa [tailState, G, result, compileCore, graphGuard, eventGuardOf,
          sem, event, hnode, added] using cfg
      have hterminalTail :
          Terminal
            (BuildResult.graph
              (compileCore k fresh.2 normalized tailState))
            cfgTail.1 := by
        simpa [cfgTail, tailState, G, result, compileCore, graphGuard,
          eventGuardOf, sem, event, hnode, added] using hterminal
      have hagreeTail :
          StoreAgree tailState
            (VEnv.cons (x := x) (τ := .sealed who b) value env)
            cfgTail.1.store := by
        intro name bindTy h
        simpa [tailState, cfgTail, graphGuard, eventGuardOf] using
          hagreeAdded h
      rcases
          sourceReplay_compileCore
            (VEnv.cons (x := x) (τ := .sealed who b) value env) k
            fresh.2 normalized tailState cfgTail hterminalTail
            hagreeTail with
        ⟨labels, final, htail, hfinalTerminal, hctx, hagreeFinal⟩
      refine ⟨.commit x who value :: labels, final, ?_, hfinalTerminal, ?_⟩
      · exact SourceConfig.LabeledStar.cons hstep htail
      · refine ⟨hctx, ?_⟩
        intro name bindTy h
        simpa [cfgTail, tailState, G, result, compileCore, graphGuard,
          eventGuardOf, sem, event, hnode, added] using
          hagreeFinal h
  | Γ, env, .reveal (b := b) y who x hx k, fresh, normalized, state, cfg, hterminal,
      hagree => by
      let sourceField := state.fieldOf hx
      let sem := NodeSem.reveal (Player := P) (L := L) sourceField
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
      let result :=
        compileCore (VegasCore.reveal y who x hx k) fresh normalized state
      let G : Graph P L := BuildResult.graph result
      have hidx : state.nodes.length < G.nodeCount := by
        have hlenNodes :=
          compileCore_nodes_length
            (VegasCore.reveal y who x hx k) fresh normalized state
        change state.nodes.length <
          (compileCore (VegasCore.reveal y who x hx k) fresh normalized
            state).nodes.length
        rw [hlenNodes]
        simp [VegasCore.instrCount]
      let node : Fin G.nodeCount := ⟨state.nodes.length, hidx⟩
      have htarget : G.nodeTarget node = state.nextField := by
        simp [G, result, node, BuildResult.graph, Graph.nodeTarget,
          BuildState.nextField, BuildState.nextNode,
          compileCore_initialFields]
      have hrow :
          G.nodes[(node : Nat)]? = some event := by
        change
          (compileCore (VegasCore.reveal y who x hx k) fresh normalized
            state).nodes[state.nodes.length]? = some event
        simpa [compileCore, sourceField, sem, event, hnode, added] using
          compileCore_added_head_get?
            (state := state) (name := y) (bindTy := .pub b)
            (sem := sem) (hfresh := fresh.1) (hnode := hnode)
            k fresh.2 normalized
      have hvalidDone : ValidDoneValues G cfg.1 := by
        simpa [G, result] using
          reachable_validDoneValues
            (compileCore (VegasCore.reveal y who x hx k) fresh normalized
              state).graphWF
            cfg.2
      rcases hvalidDone node (hterminal node) with
        ⟨row, hrowValid, hvalid⟩
      have hrowEq : row = event :=
        Option.some.inj (hrowValid.symm.trans hrow)
      subst row
      change
        (match event.sem with
        | .sample dist =>
            ∃ value : L.Val dist.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) dist.ty =
                some value ∧
              ∃ readEnv : ReadEnv L dist.reads,
                ReadEnv.ofStore? cfg.1.store dist.reads = some readEnv ∧
                value ∈ (dist.eval readEnv).support
        | .commit _ guard =>
            ∃ value : L.Val guard.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) guard.ty =
                some value ∧
              ∃ readEnv : ReadEnv L guard.choiceReads,
                ReadEnv.ofStore? cfg.1.store guard.choiceReads =
                  some readEnv ∧
                guard.eval value readEnv = true
        | .reveal source =>
            ∃ value : L.Val event.ty,
              Store.getAs cfg.1.store (G.nodeTarget node) event.ty =
                some value ∧
              Store.getAs cfg.1.store source event.ty = some value) at hvalid
      dsimp [event, sem] at hvalid
      rcases hvalid with ⟨value, htargetValue, hsourceValue⟩
      have henvValue :
          value = VEnv.get (τ := .sealed who b) env hx := by
        have hsourceAgree := hagree hx
        exact Option.some.inj (hsourceValue.symm.trans hsourceAgree)
      subst value
      have hstep :
          LStep
            ({ ctx := Γ, env := env,
               cont := VegasCore.reveal y who x hx k } : SourceConfig P L)
            (.reveal y who x (VEnv.get (τ := .sealed who b) env hx))
            { ctx := (y, .pub b) :: Γ,
              env := VEnv.cons (x := y) (τ := .pub b)
                (VEnv.get (τ := .sealed who b) env hx) env,
              cont := k } := by
        exact LStep.reveal hx k
      have hreadNext :
          Store.getAs cfg.1.store state.nextField b =
            some (VEnv.get (τ := .sealed who b) env hx) := by
        simpa [htarget] using htargetValue
      have hagreeAdded :
          StoreAgree added.1
            (VEnv.cons (x := y) (τ := .pub b)
              (VEnv.get (τ := .sealed who b) env hx) env)
            cfg.1.store :=
        hagree.addEvent_of_getAs y (.pub b) sem fresh.1 hnode
          (VEnv.get (τ := .sealed who b) env hx) hreadNext
      let cfgTail :
          ReachableConfig
            (BuildResult.graph
              (compileCore k fresh.2 normalized added.1)) := by
        simpa [G, result, compileCore, sourceField, sem, event, hnode,
          added] using cfg
      have hterminalTail :
          Terminal
            (BuildResult.graph
              (compileCore k fresh.2 normalized added.1))
            cfgTail.1 := by
        simpa [cfgTail, G, result, compileCore, sourceField, sem, event,
          hnode, added] using hterminal
      rcases
          sourceReplay_compileCore
            (VEnv.cons (x := y) (τ := .pub b)
              (VEnv.get (τ := .sealed who b) env hx) env) k
            fresh.2 normalized added.1 cfgTail hterminalTail
            hagreeAdded with
        ⟨labels, final, htail, hfinalTerminal, hctx, hagreeFinal⟩
      refine
        ⟨.reveal y who x (VEnv.get (τ := .sealed who b) env hx) ::
          labels, final, ?_,
          hfinalTerminal, ?_⟩
      · exact SourceConfig.LabeledStar.cons hstep htail
      · refine ⟨hctx, ?_⟩
        intro name bindTy h
        simpa [cfgTail, G, result, compileCore, sourceField, sem, event,
          hnode, added] using hagreeFinal h

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

/-- **Forward generation.** A terminal source run can be replayed in graph
source order, yielding a reachable terminal graph configuration whose store
reconstructs the run's terminal source environment through the compiler
dictionary. -/
theorem sourceRun_reachableConfig
    (g : GraphProgram P L)
    {labels : List (Label P L)} {final : SourceConfig P L}
    (hrun : SourceConfig.LabeledStar (sourceStart g) labels final)
    (hterminal : final.IsTerminal) :
    let result := buildResult g
    ∃ hctx : final.ctx = result.terminalCtx,
      ∃ state : ReachableConfig result.graph,
        Terminal result.graph state.1 ∧
        ∃ available :
          ∀ {name bindTy}
            (h : VHasVar result.terminalCtx name bindTy),
            ∃ value,
              Store.getAs state.1.store
                (result.terminalState.fieldOf h) bindTy.base =
                  some value,
          sourceEnvOfStore result.terminalState state.1.store available =
            cast (congrArg (VEnv L) hctx) final.env := by
  let init := initialState g.Γ g.env g.wctx
  let state := BuildState.fromInitial init
  let result := compileCore g.prog g.fresh g.normalized state
  let G := BuildResult.graph result
  let cfg₀ : Config G := Config.initial G
  have hrun' :
      SourceConfig.LabeledStar
        ({ ctx := g.Γ, env := g.env, cont := g.prog } :
          SourceConfig P L)
        labels final := by
    simpa [sourceStart] using hrun
  have hdone₀ : DonePrefix cfg₀ state.nodes.length := by
    simpa [cfg₀, G, result, state, init, BuildState.fromInitial_nodes] using
      DonePrefix.initial G
  have hagree₀ : StoreAgree state g.env cfg₀.store := by
    intro name bindTy h
    simpa [cfg₀, G, result, state, init, Config.initial,
      BuildResult.graph, BuildState.fromInitial,
      compileCore_initialFields] using
      initialState_initialStore_get
        (env := g.env) (wctx := g.wctx) result.nodes h
  rcases
      StoreAgree_run_reachable_compileCore
        hrun' g.fresh g.normalized state cfg₀ hdone₀
        Reachable.initial hagree₀ hterminal with
    ⟨hctx, terminalCfg, hreach, hterminalGraph, hagree⟩
  let reachableState : ReachableConfig result.graph := ⟨terminalCfg, hreach⟩
  let available :
      ∀ {name bindTy}
        (h : VHasVar result.terminalCtx name bindTy),
        ∃ value,
          Store.getAs reachableState.1.store
            (result.terminalState.fieldOf h) bindTy.base = some value := by
    intro name bindTy h
    exact ⟨_, hagree h⟩
  refine ⟨hctx, reachableState, hterminalGraph, available, ?_⟩
  simpa [reachableState] using
    sourceEnvOfStore_eq_of_storeAgree
      (state := result.terminalState)
      (env := cast (congrArg (VEnv L) hctx) final.env)
      (store := reachableState.1.store)
      hagree
      available

/-- A certificate packaging the canonical source-order replay of a reachable
terminal graph state. `sourceReplay_exists_of_reachableConfig` constructs this
certificate from reachability; `sourceRun_of_reachableConfig` exposes the
Prop-level reverse theorem directly. -/
structure SourceReplay
    (g : GraphProgram P L)
    (state : ReachableConfig (buildResult g).graph)
    (hterminal : Terminal (buildResult g).graph state.1) where
  labels : List (Label P L)
  final : SourceConfig P L
  run : SourceConfig.LabeledStar (sourceStart g) labels final
  sourceTerminal : final.IsTerminal
  envEq :
    ∃ hctx : final.ctx = (buildResult g).terminalCtx,
      ∃ available :
        ∀ {name bindTy}
          (h : VHasVar (buildResult g).terminalCtx name bindTy),
          ∃ value,
            Store.getAs state.1.store
              ((buildResult g).terminalState.fieldOf h) bindTy.base =
                some value,
        sourceEnvOfStore (buildResult g).terminalState state.1.store
            available =
          cast (congrArg (VEnv L) hctx) final.env

/-- Any reachable terminal compiled graph state can be replayed in canonical
source order. -/
theorem sourceReplay_exists_of_reachableConfig
    (g : GraphProgram P L)
    (state : ReachableConfig (buildResult g).graph)
    (hterminal : Terminal (buildResult g).graph state.1) :
    Nonempty (SourceReplay g state hterminal) := by
  let init := initialState g.Γ g.env g.wctx
  let compilerState := BuildState.fromInitial init
  let result := compileCore g.prog g.fresh g.normalized compilerState
  let replayState : ReachableConfig (BuildResult.graph result) := by
    simpa [result, compilerState, init, buildResult] using state
  have hterminalReplay :
      Terminal (BuildResult.graph result) replayState.1 := by
    simpa [replayState, result, compilerState, init, buildResult] using
      hterminal
  have hagree₀ : StoreAgree compilerState g.env replayState.1.store := by
    intro name bindTy h
    have hfield :
        compilerState.fieldOf h <
          (BuildResult.graph result).initialFields.length := by
      simpa [compilerState, init, result, BuildResult.graph,
        compileCore_initialFields] using init.fieldOf_lt h
    have hframe :
        Store.getAs replayState.1.store (compilerState.fieldOf h)
            bindTy.base =
          Store.getAs (BuildResult.graph result).initialStore
            (compilerState.fieldOf h) bindTy.base :=
      reachable_getAs_of_initial_field replayState.2 hfield
    have hinit :
        Store.getAs (BuildResult.graph result).initialStore
            (compilerState.fieldOf h) bindTy.base =
          some (g.env.get h) := by
      simpa [compilerState, init, result, BuildResult.graph,
        compileCore_initialFields] using
        initialState_initialStore_get
          (env := g.env) (wctx := g.wctx) result.nodes h
    exact hframe.trans hinit
  rcases
      sourceReplay_compileCore g.env g.prog g.fresh g.normalized
        compilerState replayState hterminalReplay hagree₀ with
    ⟨labels, final, hrun, hsourceTerminal, hctx, hagree⟩
  let available :
      ∀ {name bindTy}
        (h : VHasVar (buildResult g).terminalCtx name bindTy),
        ∃ value,
          Store.getAs state.1.store
            ((buildResult g).terminalState.fieldOf h) bindTy.base =
              some value := by
    intro name bindTy h
    let hResult :
        VHasVar result.terminalCtx name bindTy := by
      simpa [result, compilerState, init, buildResult] using h
    have hfield :
        result.terminalState.fieldOf hResult =
          (buildResult g).terminalState.fieldOf h := by
      simp [hResult, result, compilerState, init, buildResult]
    refine ⟨(cast (congrArg (VEnv L) hctx) final.env).get hResult, ?_⟩
    rw [← hfield]
    simpa [replayState, result, compilerState, init, buildResult] using
      hagree hResult
  have henv :
      sourceEnvOfStore (buildResult g).terminalState state.1.store
          available =
        cast (congrArg (VEnv L) hctx) final.env := by
    have hagreeBuild :
        StoreAgree (buildResult g).terminalState
          (cast (congrArg (VEnv L) hctx) final.env)
          state.1.store := by
      intro name bindTy h
      let hResult :
          VHasVar result.terminalCtx name bindTy := by
        simpa [result, compilerState, init, buildResult] using h
      have hfield :
          result.terminalState.fieldOf hResult =
            (buildResult g).terminalState.fieldOf h := by
        simp [hResult, result, compilerState, init, buildResult]
      have hget :
          (cast (congrArg (VEnv L) hctx) final.env).get hResult =
            (cast (congrArg (VEnv L) hctx) final.env).get
              (by
                simpa [result, compilerState, init, buildResult] using h) :=
        VEnv.get_eq_of_nodup result.terminalState.wctx
          (cast (congrArg (VEnv L) hctx) final.env)
          hResult
          (by
            simpa [result, compilerState, init, buildResult] using h)
      have hgetBuild :
          (cast (congrArg (VEnv L) hctx) final.env).get hResult =
            (cast (congrArg (VEnv L) hctx) final.env).get h := by
        simpa [result, compilerState, init, buildResult] using hget
      rw [← hfield]
      have hread :
          Store.getAs state.1.store (result.terminalState.fieldOf hResult)
              bindTy.base =
            some ((cast (congrArg (VEnv L) hctx) final.env).get hResult) := by
        simpa [replayState, result, compilerState, init, buildResult] using
          hagree hResult
      exact hread.trans (congrArg some hgetBuild)
    exact
      sourceEnvOfStore_eq_of_storeAgree
        (state := (buildResult g).terminalState)
        (env := cast (congrArg (VEnv L) hctx) final.env)
        (store := state.1.store)
        hagreeBuild
        available
  exact
    ⟨{ labels := labels
       final := final
       run := by
         simpa [sourceStart] using hrun
       sourceTerminal := hsourceTerminal
       envEq := ⟨hctx, available, henv⟩ }⟩

/-- Reverse generation from an already-packaged replay certificate. -/
theorem sourceRun_of_replay
    (g : GraphProgram P L)
    (state : ReachableConfig (buildResult g).graph)
    (hterminal : Terminal (buildResult g).graph state.1)
    (replay : SourceReplay g state hterminal) :
    ∃ labels : List (Label P L),
      ∃ final : SourceConfig P L,
        SourceConfig.LabeledStar (sourceStart g) labels final ∧
        final.IsTerminal ∧
        ∃ hctx : final.ctx = (buildResult g).terminalCtx,
          ∃ available :
            ∀ {name bindTy}
              (h : VHasVar (buildResult g).terminalCtx name bindTy),
              ∃ value,
                Store.getAs state.1.store
                  ((buildResult g).terminalState.fieldOf h) bindTy.base =
                    some value,
            sourceEnvOfStore (buildResult g).terminalState state.1.store
                available =
              cast (congrArg (VEnv L) hctx) final.env := by
  exact
    ⟨replay.labels, replay.final, replay.run, replay.sourceTerminal,
      replay.envEq⟩

/-- **Reverse generation.** Every reachable terminal compiled graph state
comes from a terminal source run in canonical source order, with the same
environment after graph-store readback. -/
theorem sourceRun_of_reachableConfig
    (g : GraphProgram P L)
    (state : ReachableConfig (buildResult g).graph)
    (hterminal : Terminal (buildResult g).graph state.1) :
    ∃ labels : List (Label P L),
      ∃ final : SourceConfig P L,
        SourceConfig.LabeledStar (sourceStart g) labels final ∧
        final.IsTerminal ∧
        ∃ hctx : final.ctx = (buildResult g).terminalCtx,
          ∃ available :
            ∀ {name bindTy}
              (h : VHasVar (buildResult g).terminalCtx name bindTy),
              ∃ value,
                Store.getAs state.1.store
                  ((buildResult g).terminalState.fieldOf h) bindTy.base =
                    some value,
            sourceEnvOfStore (buildResult g).terminalState state.1.store
                available =
              cast (congrArg (VEnv L) hctx) final.env :=
by
  rcases sourceReplay_exists_of_reachableConfig g state hterminal with
    ⟨replay⟩
  exact sourceRun_of_replay g state hterminal replay

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
