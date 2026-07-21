/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Commit

/-!
# Frontier query laws at source commits

This file is the first frontier-to-source query layer.  Projecting a frontier
legal-action law to the value assigned at the current compiled source-order
node gives a source query law: every concrete value in its support satisfies
the source commit guard.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- If the projected frontier legal-action law can assign `value` to the
current source-order node, then the corresponding source value is legal for the
current source commit guard.

This is the unconditioned frontier-to-source query fact: it extracts an action
from support of the projected law, reads its node value, reflects frontier
commit availability back through the supported internal closure, and obtains
the source guard proof needed by a source strategy query. -/
theorem sourceLegal_of_projected_nodeValue_support
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
    (hvalueSupport :
      some value ∈
        (Math.ProbabilityMassFunction.pushforward
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
            | none => none)).support) :
    let sourceValue : L.Val b :=
      cast
        (congrArg L.Val
          (currentNodeType program replay hnode))
        value
    evalGuard (Player := P) (L := L) guard sourceValue
      ((env.toView who).eraseEnv) = true := by
  let compiled := compile program.core
  let view :=
    EventGraph.frontierRoundView
      (primitiveMachineSpec compiled) presentation semantics
  let hty := currentNodeType program replay hnode
  let sourceValue : L.Val b := cast (congrArg L.Val hty) value
  let project :
      Machine.RoundView.BoundedLegalAction view horizon h.lastState →
        Option (L.Val ((compile program.core).graph.nodeRow node).ty) :=
    fun action =>
      match action.1 who with
      | some frontierAction => frontierAction.value? node
      | none => none
  have hvalueSupport' :
      some value ∈
        (Math.ProbabilityMassFunction.pushforward
          (Machine.RoundView.legalActionLaw view horizon σ h hterm)
          project).support := by
    exact hvalueSupport
  rw [Math.ProbabilityMassFunction.pushforward] at hvalueSupport'
  rcases (PMF.mem_support_map_iff project
      (Machine.RoundView.legalActionLaw view horizon σ h hterm)
      (some value)).mp hvalueSupport' with
    ⟨action, _hactionSupport, hproject⟩
  dsimp [project] at hproject
  have hcommitNodeRaw :
      EventGraph.CommitAvailable (compile program.core).graph
        h.lastState.state.1 who
        { node := node,
          value := (compile program.core).graph.nodeTypedValue node value } := by
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
    sourceLegal_of_available_after_internalClosure
      program replay hnode sourceValue fuel hsupport hcommit

end ToEventGraph

end Vegas
