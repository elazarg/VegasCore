/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler

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

end ToEventGraph

end Vegas
