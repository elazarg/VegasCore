/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Commit
import Vegas.Frontier.SourceFrontier.Law

/-!
# Conditioned frontier node values reflect to source legality

This file composes the frontier action-law and current commit-block facts:
a frontier action law conditioned on the current compiled node value gives a
source-legal value for the corresponding source commit.
-/

namespace Vegas

namespace ToEventGraph
namespace SourceFrontier
namespace Conditioned

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- If a supported conditioned frontier legal action lies in the fiber where the
current source-order node receives `value`, then that value satisfies the source
commit guard after casting along the compiler's current-node type equality. -/
theorem sourceLegal_of_conditioned_nodeValue
    (program : WFProgram P L)
    (presentation :
      EventGraph.CheckpointPresentation (compile program.core).graph)
    (semantics :
      EventGraph.FrontierRoundSemantics
        (primitiveMachineSpec (compile program.core)) presentation)
    {horizon : Nat}
    [∀ player,
      Fintype
        (Option
          ((EventGraph.frontierRoundView
              (primitiveMachineSpec (compile program.core))
              presentation semantics).Act player))]
    (σ :
      Machine.RoundView.BoundedBehavioralProfile
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics) horizon)
    (h :
      Machine.RoundView.BoundedHistory
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics) horizon)
    (hterm :
      ¬ Machine.RoundView.boundedTerminal
          (EventGraph.frontierRoundView
            (primitiveMachineSpec (compile program.core))
            presentation semantics)
          horizon h.lastState)
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
    (hsupport :
      h.lastState.state ∈
        (internalClosureTransition
          (compile program.core) fuel replay.state).support)
    (value : L.Val (((compile program.core).graph.nodeRow node).ty))
    {action :
      Machine.RoundView.BoundedLegalAction
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics)
        horizon h.lastState}
    (hvalueMass :
      Math.ProbabilityMassFunction.pushforward
          (Machine.RoundView.legalActionLaw
            (EventGraph.frontierRoundView
              (primitiveMachineSpec (compile program.core))
              presentation semantics)
            horizon σ h hterm)
          (fun action :
              Machine.RoundView.BoundedLegalAction
                (EventGraph.frontierRoundView
                  (primitiveMachineSpec (compile program.core))
                  presentation semantics)
                horizon h.lastState =>
            match action.1 who with
            | some frontierAction => frontierAction.value? node
            | none => none)
          (some value) ≠ 0)
    (hactionSupport :
      action ∈
        (Math.ProbabilityMassFunction.condOn
          (Machine.RoundView.legalActionLaw
            (EventGraph.frontierRoundView
              (primitiveMachineSpec (compile program.core))
              presentation semantics)
            horizon σ h hterm)
          (fun action :
              Machine.RoundView.BoundedLegalAction
                (EventGraph.frontierRoundView
                  (primitiveMachineSpec (compile program.core))
                  presentation semantics)
                horizon h.lastState =>
            match action.1 who with
            | some frontierAction => frontierAction.value? node
            | none => none)
          (some value)).support) :
    let sourceValue : L.Val b :=
      cast
        (congrArg L.Val
          (CommitBlock.currentNodeType program replay hnode))
        value
    evalGuard (Player := P) (L := L) guard sourceValue
      ((env.toView who).eraseEnv) = true := by
  let compiled := compile program.core
  let view :=
    EventGraph.frontierRoundView
      (primitiveMachineSpec compiled) presentation semantics
  let hty := CommitBlock.currentNodeType program replay hnode
  let sourceValue : L.Val b := cast (congrArg L.Val hty) value
  let project :
      Machine.RoundView.BoundedLegalAction view horizon h.lastState →
        Option (L.Val ((compile program.core).graph.nodeRow node).ty) :=
    fun action =>
      match action.1 who with
      | some frontierAction => frontierAction.value? node
      | none => none
  have hvalueMass' :
      Math.ProbabilityMassFunction.pushforward
          (Machine.RoundView.legalActionLaw view horizon σ h hterm)
          project (some value) ≠ 0 := by
    simpa [view, project] using hvalueMass
  have hactionSupport' :
      action ∈
        (Math.ProbabilityMassFunction.condOn
          (Machine.RoundView.legalActionLaw view horizon σ h hterm)
          project (some value)).support := by
    simpa [view, project] using hactionSupport
  have hproject : project action = some value :=
    Machine.RoundView.legalActionLaw_condOn_support_project
      view horizon σ h hterm project (some value)
      hvalueMass' hactionSupport'
  dsimp [project] at hproject
  have hcommitNodeRaw :
      EventGraph.CommitAvailable (compile program.core).graph h.lastState.state.1 who
        { node := node, value := (compile program.core).graph.nodeTypedValue node value } := by
    cases hmove : action.1 who with
    | none =>
        simp [hmove] at hproject
    | some frontierAction =>
        have hnodeValue : frontierAction.value? node = some value := by
          simpa [hmove] using hproject
        exact
          EventGraph.frontierRoundView_commitAvailable_of_boundedLegal_value
            (primitiveMachineSpec (compile program.core))
            presentation semantics hterm hmove hnodeValue
  have hcommitNode :
      EventGraph.CommitAvailable compiled.graph h.lastState.state.1 who
        { node := node, value := compiled.graph.nodeTypedValue node value } := by
    simpa [compiled] using hcommitNodeRaw
  have htyped :
      compiled.graph.nodeTypedValue node value =
        ({ ty := b, value := sourceValue } :
          EventGraph.TypedValue L) := by
    cases hty
    rfl
  have hcommit :
      EventGraph.CommitAvailable compiled.graph h.lastState.state.1 who
        { node := node, value := { ty := b, value := sourceValue } } := by
    simpa [htyped] using hcommitNode
  exact
    CommitBlock.sourceLegal_of_available_after_internalClosure
      program replay hnode sourceValue fuel hsupport hcommit

end Conditioned
end SourceFrontier
end ToEventGraph

end Vegas
