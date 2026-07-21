/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Core.Trace
import Vegas.EventGraph.VisibleOrder

/-!
# Source-to-graph bridge: node correspondence

This module begins the bridge tying a source program to the event graph it
compiles to. The structural facts here are that compilation consumes the source
program head-first, emitting exactly one node per `sample`/`commit`/`reveal`
instruction (`addEvent`) and never touching nodes already emitted:

* `compileCore_nodes_prefix` — the nodes already built stay a prefix of the
  result, so a node's id is stable through the rest of compilation;
* `compileCore_nodes_length` — compilation appends exactly `prog.instrCount`
  nodes, so the node a source instruction emits sits at a position determined by
  how many instructions preceded it.

Together these are the backbone for the position↔node-id correspondence the
trace-level bridge needs.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The number of primitive instructions in a program — equivalently, the number
of graph nodes its compilation emits. -/
def VegasCore.instrCount {Γ : VCtx P L} : VegasCore P L Γ → Nat
  | .ret _ => 0
  | .sample _ _ k => k.instrCount + 1
  | .commit _ _ _ k => k.instrCount + 1
  | .reveal _ _ _ _ k => k.instrCount + 1

/-- The owner of each instruction's node: `none` for the public events
(`sample`, `reveal`), and `some who` for a commit by `who`. This is the
owner the corresponding graph node carries, fixed by the instruction alone. -/
def VegasCore.instrOwners {Γ : VCtx P L} :
    VegasCore P L Γ → List (Option P)
  | .ret _ => []
  | .sample _ _ k => none :: k.instrOwners
  | .commit _ who _ k => some who :: k.instrOwners
  | .reveal _ _ _ _ k => none :: k.instrOwners

namespace SourcePlayerEvent.Kind

/-- The graph node owner corresponding to a source order-trace event kind.
Samples and reveals compile to public nodes; commits compile to nodes owned by
the committing player. -/
def graphOwner : SourcePlayerEvent.Kind P → Option P
  | .sample => none
  | .ownCommit owner => some owner
  | .otherCommit owner => some owner
  | .reveal _ => none

end SourcePlayerEvent.Kind

namespace VegasCore

/-- Projecting a player's source order-trace skeleton to graph node owners
recovers the source instruction-owner sequence. This forgets the own/other
distinction and the sample/reveal distinction, exactly matching the graph's
owner-based readability structure. -/
theorem orderTrace_graphOwners_eq_instrOwners {Γ : VCtx P L}
    (prog : VegasCore P L Γ) (who : P) :
    (prog.orderTrace who).map SourcePlayerEvent.Kind.graphOwner =
      prog.instrOwners := by
  induction prog with
  | ret _ =>
      rfl
  | sample _ _ tail ih =>
      simp [VegasCore.orderTrace, VegasCore.instrOwners,
        SourcePlayerEvent.Kind.graphOwner, ih]
  | commit _ owner _ tail ih =>
      by_cases hwho : who = owner
      · subst who
        simp [VegasCore.orderTrace, VegasCore.instrOwners,
          SourcePlayerEvent.Kind.graphOwner, ih]
      · simp [VegasCore.orderTrace, VegasCore.instrOwners,
          SourcePlayerEvent.Kind.graphOwner, ih, hwho]
  | reveal _ _ _ _ tail ih =>
      simp [VegasCore.orderTrace, VegasCore.instrOwners,
        SourcePlayerEvent.Kind.graphOwner, ih]

end VegasCore

namespace ToEventGraph

/-- Compiling a program suffix only appends nodes: the nodes already built remain
a prefix of the result. -/
theorem compileCore_nodes_prefix :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (normalized : NormalizedDists prog) →
      (state : BuildState P L Γ) →
      state.nodes <+: (compileCore prog fresh normalized state).nodes
  | _, .ret _payoffs, _fresh, _normalized, _state => by
      simp only [compileCore]
      exact List.prefix_rfl
  | _, .sample name dist tail, fresh, normalized, state => by
      simp only [compileCore]
      refine List.IsPrefix.trans ?_ (compileCore_nodes_prefix tail _ _ _)
      simp only [BuildState.addEvent_nodes]
      exact List.prefix_append _ _
  | _, .commit name who guard tail, fresh, normalized, state => by
      simp only [compileCore]
      refine List.IsPrefix.trans ?_ (compileCore_nodes_prefix tail _ _ _)
      simp only [BuildState.addEvent_nodes]
      exact List.prefix_append _ _
  | _, .reveal name who source sourceProof tail, fresh, normalized, state => by
      simp only [compileCore]
      refine List.IsPrefix.trans ?_ (compileCore_nodes_prefix tail _ _ _)
      simp only [BuildState.addEvent_nodes]
      exact List.prefix_append _ _

/-- Compiling a program suffix appends exactly `prog.instrCount` nodes. -/
theorem compileCore_nodes_length :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (normalized : NormalizedDists prog) →
      (state : BuildState P L Γ) →
      (compileCore prog fresh normalized state).nodes.length =
        state.nodes.length + prog.instrCount
  | _, .ret _payoffs, _fresh, _normalized, _state => by
      simp [compileCore, VegasCore.instrCount]
  | _, .sample name dist tail, fresh, normalized, state => by
      simp only [compileCore, VegasCore.instrCount]
      rw [compileCore_nodes_length tail _ _ _]
      simp only [BuildState.addEvent_nodes, List.length_append, List.length_cons,
        List.length_nil]
      omega
  | _, .commit name who guard tail, fresh, normalized, state => by
      simp only [compileCore, VegasCore.instrCount]
      rw [compileCore_nodes_length tail _ _ _]
      simp only [BuildState.addEvent_nodes, List.length_append, List.length_cons,
        List.length_nil]
      omega
  | _, .reveal name who source sourceProof tail, fresh, normalized, state => by
      simp only [compileCore, VegasCore.instrCount]
      rw [compileCore_nodes_length tail _ _ _]
      simp only [BuildState.addEvent_nodes, List.length_append, List.length_cons,
        List.length_nil]
      omega

/-- The owners of the compiled nodes are exactly the owners of the source
instructions: compilation maps each instruction to a node carrying that
instruction's owner. This is the owner sequence the readable-output bridge needs
— `NodeOutputReadableBy`/`readableOrder` depend on the graph only through node
owners. -/
theorem compileCore_nodes_owners :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (normalized : NormalizedDists prog) →
      (state : BuildState P L Γ) →
      (compileCore prog fresh normalized state).nodes.map EventGraph.EventNode.owner =
        state.nodes.map EventGraph.EventNode.owner ++ prog.instrOwners
  | _, .ret _payoffs, _fresh, _normalized, _state => by
      simp [compileCore, VegasCore.instrOwners]
  | _, .sample name dist tail, fresh, normalized, state => by
      simp only [compileCore, VegasCore.instrOwners]
      rw [compileCore_nodes_owners tail _ _ _]
      simp [BuildState.addEvent_nodes, BindTy.owner_public, List.append_assoc]
  | _, .commit name who guard tail, fresh, normalized, state => by
      simp only [compileCore, VegasCore.instrOwners]
      rw [compileCore_nodes_owners tail _ _ _]
      simp [BuildState.addEvent_nodes, BindTy.owner_sealed, List.append_assoc]
  | _, .reveal name who source sourceProof tail, fresh, normalized, state => by
      simp only [compileCore, VegasCore.instrOwners]
      rw [compileCore_nodes_owners tail _ _ _]
      simp [BuildState.addEvent_nodes, BindTy.owner_public, List.append_assoc]

/-- **Top-level owner correspondence.** The owners of the compiled graph's nodes
are exactly the owners of the source program's instructions, in order. Since
`NodeOutputReadableBy who node` is `(G.nodeRow node).owner = none ∨ = some who`,
this pins the graph's entire readability structure to the source. -/
theorem compile_graph_nodes_owners (g : GraphProgram P L) :
    (compile g).graph.nodes.map EventGraph.EventNode.owner = g.prog.instrOwners := by
  unfold compile
  rw [compileCore_nodes_owners]
  simp [BuildState.fromInitial_nodes]

/-- Reading node owners along the compiled graph's canonical order recovers the
source program's instruction owners, in order. -/
theorem compile_graph_nodeOrder_owners (g : GraphProgram P L) :
    ((compile g).graph.nodeOrder.map fun n => ((compile g).graph.nodeRow n).owner) =
      g.prog.instrOwners := by
  rw [EventGraph.Graph.nodeOrder_map_owner, compile_graph_nodes_owners]

/-- Reading node owners along the compiled graph's canonical order recovers the
source order-trace skeleton after projecting source event kinds to graph node
owners. -/
theorem compile_graph_nodeOrder_owners_eq_orderTrace_graphOwners
    (g : GraphProgram P L) (who : P) :
    ((compile g).graph.nodeOrder.map
        fun n => ((compile g).graph.nodeRow n).owner) =
      (g.prog.orderTrace who).map SourcePlayerEvent.Kind.graphOwner :=
  (compile_graph_nodeOrder_owners g).trans
    (g.prog.orderTrace_graphOwners_eq_instrOwners who).symm

/-- **Trace-match bridge (owner level).** The owners read along player `who`'s
readable-output order of the compiled graph are exactly the readable owners of
the source program, in order. This is the source↔graph correspondence the
readable-output schedule quotient compares: the graph's per-player readable order
is determined by the source. -/
theorem compile_graph_readableOrder_owners (g : GraphProgram P L) (who : P) :
    (((compile g).graph.readableOrder who (compile g).graph.nodeOrder).map
        fun n => ((compile g).graph.nodeRow n).owner) =
      g.prog.instrOwners.filter fun o => decide (o = none ∨ o = some who) := by
  rw [EventGraph.Graph.readableOrder_map_owner,
    EventGraph.Graph.nodeOrder_map_owner, compile_graph_nodes_owners]

/-- The compiled graph's readable-output owner sequence for `who` is the
source order-trace skeleton projected to graph node owners and then restricted
to owners whose output value `who` can read. -/
theorem compile_graph_readableOrder_owners_eq_orderTrace_readableGraphOwners
    (g : GraphProgram P L) (who : P) :
    (((compile g).graph.readableOrder who (compile g).graph.nodeOrder).map
        fun n => ((compile g).graph.nodeRow n).owner) =
      ((g.prog.orderTrace who).map
        SourcePlayerEvent.Kind.graphOwner).filter
          fun o => decide (o = none ∨ o = some who) := by
  rw [compile_graph_readableOrder_owners,
    g.prog.orderTrace_graphOwners_eq_instrOwners who]

end ToEventGraph

end Vegas
