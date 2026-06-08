/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.SourceCompletion

/-!
# Source values as frontier actions

A frontier local move is a total assignment over the player's ready commit
frontier.  A single source query therefore has to be extended to a full
frontier action by filling the other ready nodes with live default values.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace CommitAvailable

/-- Commit availability exposes the corresponding ready commit node. -/
theorem readyCommitNode
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {node : Fin G.nodeCount} {value : L.Val (G.nodeRow node).ty}
    (havailable :
      CommitAvailable G cfg who
        { node := node, value := G.nodeTypedValue node value }) :
    ReadyCommitNode G cfg who node := by
  rcases havailable with ⟨step⟩
  exact ⟨step.row, step.guard, step.row_get, step.sem_eq, step.ready⟩

end CommitAvailable

namespace FrontierAction

/-- Override one node value in a frontier action. -/
noncomputable def setValue
    {G : Graph Player L} {who : Player}
    (action : FrontierAction G who)
    (node : Fin G.nodeCount)
    (value : L.Val (G.nodeRow node).ty) :
    FrontierAction G who where
  value? := fun query =>
    if hquery : query = node then
      some
        (cast
          (congrArg (fun n => L.Val (G.nodeRow n).ty) hquery.symm)
          value)
    else
      action.value? query

@[simp] theorem setValue_value?_self
    {G : Graph Player L} {who : Player}
    (action : FrontierAction G who)
    (node : Fin G.nodeCount)
    (value : L.Val (G.nodeRow node).ty) :
    (action.setValue node value).value? node = some value := by
  simp [setValue]

/-- Replacing the value assigned to one ready commit node with another
available value preserves local frontier-action availability. -/
theorem setValue_available
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {action : FrontierAction G who}
    (havailable : FrontierAction.Available G cfg who action)
    {node : Fin G.nodeCount} {value : L.Val (G.nodeRow node).ty}
    (hcommit :
      CommitAvailable G cfg who
        { node := node, value := G.nodeTypedValue node value }) :
    FrontierAction.Available G cfg who (action.setValue node value) := by
  classical
  intro query
  by_cases hready : ReadyCommitNode G cfg who query
  · rw [dif_pos hready]
    by_cases hquery : query = node
    · subst query
      exact ⟨value, by simp [setValue], hcommit⟩
    · have hbase := havailable query
      rw [dif_pos hready] at hbase
      rcases hbase with ⟨baseValue, hbaseValue, hbaseCommit⟩
      refine ⟨baseValue, ?_, hbaseCommit⟩
      simp [setValue, hquery, hbaseValue]
  · rw [dif_neg hready]
    by_cases hquery : query = node
    · subst query
      exact False.elim
        (hready (CommitAvailable.readyCommitNode hcommit))
    · have hbase := havailable query
      rw [dif_neg hready] at hbase
      simpa [setValue, hquery] using hbase

end FrontierAction
end EventGraph

namespace ToEventGraph
namespace SourceFrontier
namespace Action

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A source-legal current commit value can be extended to a full available
frontier local action after internal closure.  Other ready commit nodes are
filled by the canonical live frontier action. -/
theorem sourceLegal_extends_to_available_frontierAction_after_internalClosure
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (compile program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length)
    (value : L.Val b)
    (hguard :
      evalGuard (Player := P) (L := L) guard value
        ((env.toView who).eraseEnv) = true)
    (fuel : Nat)
    {dst : (PrimitiveMachine (compile program.core)).State}
    (hsupport :
      dst ∈
        (internalClosureTransition
          (compile program.core) fuel replay.state).support) :
    ∃ frontierAction :
        EventGraph.FrontierAction
          (compile program.core).graph who,
      EventGraph.FrontierAction.Available
          (compile program.core).graph dst.1 who
          frontierAction ∧
        frontierAction.value? node =
          some
            (cast
              (congrArg L.Val
                (CommitBlock.currentNodeType
                  program replay hnode).symm)
              value) := by
  let compiled := compile program.core
  let G := compiled.graph
  let hty := CommitBlock.currentNodeType program replay hnode
  let nodeValue : L.Val (G.nodeRow node).ty :=
    cast (congrArg L.Val hty.symm) value
  let base : EventGraph.FrontierAction G who :=
    EventGraph.liveFrontierAction G dst.1 compiled.graphWF
      (EventGraph.reachable_storeCoherent compiled.graphWF dst.2)
      (compile_guardLive program) who
  have hbaseAvailable :
      EventGraph.FrontierAction.Available G dst.1 who base :=
    EventGraph.liveFrontierAction_available compiled.graphWF
      (EventGraph.reachable_storeCoherent compiled.graphWF dst.2)
      (compile_guardLive program) who
  have hcommitSource :
      EventGraph.CommitAvailable G dst.1 who
        { node := node, value := { ty := b, value := value } } := by
    simpa [compiled, G] using
      CommitBlock.available_after_internalClosure_of_sourceLegal
        program replay hnode value hguard fuel hsupport
  have htyped :
      ({ ty := b, value := value } : EventGraph.TypedValue L) =
        G.nodeTypedValue node nodeValue := by
    cases hty
    rfl
  have hcommit :
      EventGraph.CommitAvailable G dst.1 who
        { node := node, value := G.nodeTypedValue node nodeValue } := by
    simpa [htyped] using hcommitSource
  refine
    ⟨base.setValue node nodeValue,
      EventGraph.FrontierAction.setValue_available
        hbaseAvailable hcommit,
      ?_⟩
  simp [nodeValue]

end Action
end SourceFrontier
end ToEventGraph

end Vegas
