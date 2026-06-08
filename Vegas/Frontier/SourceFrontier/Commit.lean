/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ValueBridge
import Vegas.Frontier.RoundView.InternalClosure

/-!
# Source/frontier commit-block bridge

This file is the local commit-node part of the raw source/frontier proof.

The central situation is a source prefix that has replayed to a source `commit`
point.  The compiler identifies the current source-order graph node; after
frontier internal closure, legal source values and available frontier commit
actions at that node are the same predicate, up to the compiler's node-type
equality.
-/

namespace Vegas

namespace ToEventGraph
namespace SourceFrontier
namespace CommitBlock

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The current source-order commit node has the source commit value type. -/
theorem currentNodeType
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
    (hnode : (node : Nat) = replay.compilerState.nodes.length) :
    ((compile program.core).graph.nodeRow node).ty = b :=
  SourcePrefixReplay.currentCommitNode_ty_eq program.core replay hnode

/-- Source legality at the current commit node persists through supported
frontier internal closure as compiled commit availability. -/
theorem available_after_internalClosure_of_sourceLegal
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
    EventGraph.CommitAvailable
      (compile program.core).graph dst.1 who
      { node := node, value := { ty := b, value := value } } := by
  have hbefore :
      EventGraph.CommitAvailable
        (compile program.core).graph replay.state.1 who
        { node := node, value := { ty := b, value := value } } := by
    exact
      (SourcePrefixReplay.sourceCommitMenu_iff_commitAvailable
        program.core replay hnode value).mp hguard
  exact
    commitAvailable_persist_after_internalClosureTransition_support
      (compile program.core) fuel hbefore hsupport

/-- Compiled commit availability after supported frontier internal closure
reflects back to source guard legality for the current source-order node. -/
theorem sourceLegal_of_available_after_internalClosure
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
    (fuel : Nat)
    {dst : (PrimitiveMachine (compile program.core)).State}
    (hsupport :
      dst ∈
        (internalClosureTransition
          (compile program.core) fuel replay.state).support)
    (havailable :
      EventGraph.CommitAvailable
        (compile program.core).graph dst.1 who
        { node := node, value := { ty := b, value := value } }) :
    evalGuard (Player := P) (L := L) guard value
      ((env.toView who).eraseEnv) = true := by
  rcases SourcePrefixReplay.readyCommitNode program.core replay with
    ⟨currentNode, hcurrentNode, hreadyCommit⟩
  have hnodeEq : currentNode = node :=
    Fin.ext (hcurrentNode.trans hnode.symm)
  subst currentNode
  have hbefore :
      EventGraph.CommitAvailable
        (compile program.core).graph replay.state.1 who
        { node := node, value := { ty := b, value := value } } :=
    commitAvailable_reflect_before_internalClosureTransition_support
      (compile program.core) fuel hreadyCommit.ready hsupport havailable
  exact
    SourcePrefixReplay.source_guard_of_commitAvailable
      program.core replay hnode value hbefore

/-- Source menu membership is exactly current-node compiled availability after
supported frontier internal closure. -/
theorem sourceMenu_iff_available_after_internalClosure
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
    (fuel : Nat)
    {dst : (PrimitiveMachine (compile program.core)).State}
    (hsupport :
      dst ∈
        (internalClosureTransition
          (compile program.core) fuel replay.state).support) :
    value ∈ SourceCommitMenu (L := L) who guard env ↔
      EventGraph.CommitAvailable
        (compile program.core).graph dst.1 who
        { node := node, value := { ty := b, value := value } } := by
  constructor
  · intro hguard
    exact
      available_after_internalClosure_of_sourceLegal
        program replay hnode value hguard fuel hsupport
  · intro havailable
    exact
      sourceLegal_of_available_after_internalClosure
        program replay hnode value fuel hsupport havailable

/-- If a frontier action available after internal closure assigns a value to the
current source-order node, that value is source-legal after casting along the
compiler's node-type equality. -/
theorem sourceLegal_of_frontierActionValue_after_internalClosure
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
    (fuel : Nat)
    {dst : (PrimitiveMachine (compile program.core)).State}
    (hsupport :
      dst ∈
        (internalClosureTransition
          (compile program.core) fuel replay.state).support)
    (frontierAction :
      EventGraph.FrontierAction (compile program.core).graph who)
    (hfrontierAvailable :
      EventGraph.FrontierAction.Available
        (compile program.core).graph dst.1 who frontierAction)
    (value : L.Val (((compile program.core).graph.nodeRow node).ty))
    (hvalue : frontierAction.value? node = some value) :
    let sourceValue : L.Val b :=
      cast (congrArg L.Val (currentNodeType program replay hnode)) value
    evalGuard (Player := P) (L := L) guard sourceValue
      ((env.toView who).eraseEnv) = true := by
  let hty := currentNodeType program replay hnode
  let sourceValue : L.Val b := cast (congrArg L.Val hty) value
  have hcommitNode :
      EventGraph.CommitAvailable
        (compile program.core).graph dst.1 who
        { node := node,
          value := (compile program.core).graph.nodeTypedValue node value } :=
    hfrontierAvailable.commitAvailable_of_value hvalue
  have htyped :
      (compile program.core).graph.nodeTypedValue node value =
        ({ ty := b, value := sourceValue } : EventGraph.TypedValue L) := by
    cases hty
    rfl
  have hcommit :
      EventGraph.CommitAvailable
        (compile program.core).graph dst.1 who
        { node := node, value := { ty := b, value := sourceValue } } := by
    simpa [htyped] using hcommitNode
  exact
    sourceLegal_of_available_after_internalClosure
      program replay hnode sourceValue fuel hsupport hcommit

end CommitBlock
end SourceFrontier
end ToEventGraph

end Vegas
