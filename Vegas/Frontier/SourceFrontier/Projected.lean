/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Action

/-!
# Projected frontier laws for source queries

This module strengthens the frontier-to-source query layer: at an active
frontier checkpoint, projection of the legal frontier action law to the current
source-order node has no `none` branch.  Together with `Query`, this is what
turns a frontier behavioral law into a genuine source query PMF.
-/

namespace Vegas

namespace ToEventGraph
namespace SourceFrontier
namespace Projected

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

omit [Fintype P] in
/-- Project a bounded frontier action to the optional value it assigns to one
commit node. -/
def nodeValueProjection
    {G : EventGraph.Graph P L}
    (spec : EventGraph.ToMachine.GraphMachineSpec G)
    (presentation : EventGraph.CheckpointPresentation G)
    (semantics :
      EventGraph.FrontierRoundSemantics spec presentation)
    {horizon : Nat}
    {state : (EventGraph.PrimitiveMachineOf spec).BoundedState horizon}
    {who : P}
    (node : Fin G.nodeCount)
    (action :
      Machine.RoundView.BoundedLegalAction
        (EventGraph.frontierRoundView spec presentation semantics)
        horizon state) :
    Option (L.Val (G.nodeRow node).ty) :=
  match action.1 who with
  | some frontierAction => frontierAction.value? node
  | none => none

omit [Fintype P] in
/-- A ready current source-order commit node remains ready after supported
frontier internal closure. -/
theorem currentNode_readyCommitNode_after_internalClosure
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
          (compile program.core) fuel replay.state).support) :
    EventGraph.ReadyCommitNode (compile program.core).graph dst.1 who node := by
  let compiled := compile program.core
  let G := compiled.graph
  rcases SourcePrefixReplay.readyCommitNode program.core replay with
    ⟨currentNode, hcurrentNode, hreadyCurrent⟩
  have hnodeEq : currentNode = node :=
    Fin.ext (hcurrentNode.trans hnode.symm)
  subst currentNode
  have hreadyAtReplay :
      EventGraph.ReadyCommitNode G replay.state.1 who node := by
    simpa [compiled, G] using hreadyCurrent
  have hcoherent :
      EventGraph.StoreCoherent G replay.state.1 :=
    EventGraph.reachable_storeCoherent compiled.graphWF replay.state.2
  rcases
      EventGraph.exists_commitValue_of_readyCommitNode
        compiled.graphWF hcoherent (compile_guardLive program)
        hreadyAtReplay with
    ⟨value, hcommitAtReplay⟩
  have hcommitAtDst :
      EventGraph.CommitAvailable G dst.1 who
        { node := node, value := G.nodeTypedValue node value } := by
    exact
      commitAvailable_persist_after_internalClosureTransition_support
        compiled fuel hcommitAtReplay (by
          simpa [compiled] using hsupport)
  exact EventGraph.CommitAvailable.readyCommitNode hcommitAtDst

/-- If the player is active and `node` is ready for that player, the legal
frontier action law cannot project to `none` at `node`. -/
theorem projected_nodeValueLaw_none_not_support_of_ready_active
    {G : EventGraph.Graph P L}
    (spec : EventGraph.ToMachine.GraphMachineSpec G)
    (presentation : EventGraph.CheckpointPresentation G)
    (semantics :
      EventGraph.FrontierRoundSemantics spec presentation)
    {horizon : Nat}
    [∀ player,
      Fintype
        (Option
          ((EventGraph.frontierRoundView
              spec presentation semantics).Act player))]
    (σ :
      Machine.RoundView.BoundedBehavioralProfile
        (EventGraph.frontierRoundView
          spec presentation semantics) horizon)
    (h :
      Machine.RoundView.BoundedHistory
        (EventGraph.frontierRoundView
          spec presentation semantics) horizon)
    (hterm :
      ¬ Machine.RoundView.boundedTerminal
          (EventGraph.frontierRoundView
            spec presentation semantics)
          horizon h.lastState)
    {who : P} {node : Fin G.nodeCount}
    (hactive :
      who ∈
        Machine.RoundView.boundedActive
          (EventGraph.frontierRoundView spec presentation semantics)
          horizon h.lastState)
    (hready :
      EventGraph.ReadyCommitNode G h.lastState.state.1 who node)
    (hnoneSupport :
      none ∈
        (Math.ProbabilityMassFunction.pushforward
          (Machine.RoundView.legalActionLaw
            (EventGraph.frontierRoundView
              spec presentation semantics)
            horizon σ h hterm)
          (nodeValueProjection spec presentation semantics
            (who := who) node)).support) :
    False := by
  let view :=
    EventGraph.frontierRoundView spec presentation semantics
  let project :
      Machine.RoundView.BoundedLegalAction view horizon h.lastState →
        Option (L.Val (G.nodeRow node).ty) :=
    nodeValueProjection spec presentation semantics (who := who) node
  have hnoneSupport' :
      none ∈
        (Math.ProbabilityMassFunction.pushforward
          (Machine.RoundView.legalActionLaw view horizon σ h hterm)
          project).support := by
    simpa [view, project] using hnoneSupport
  rw [Math.ProbabilityMassFunction.pushforward] at hnoneSupport'
  rcases (PMF.mem_support_map_iff project
      (Machine.RoundView.legalActionLaw view horizon σ h hterm)
      none).mp hnoneSupport' with
    ⟨action, _hactionSupport, hproject⟩
  dsimp [project, nodeValueProjection] at hproject
  cases hmove : action.1 who with
  | none =>
      have hnotActive :
          who ∉
            Machine.RoundView.boundedActive view horizon h.lastState := by
        simpa [view] using
          GameTheory.JointActionLegal.none action.2 hmove
      exact hnotActive (by simpa [view] using hactive)
  | some frontierAction =>
      have hlocal :
          who ∈
              Machine.RoundView.boundedActive view horizon h.lastState ∧
            frontierAction ∈
              Machine.RoundView.boundedAvailableActions
                view horizon h.lastState who := by
        simpa [view] using
          GameTheory.JointActionLegal.some action.2 hmove
      have hnotCutoff : ¬ horizon ≤ h.lastState.depth := by
        intro hcutoff
        have hempty : who ∈ (∅ : Finset P) := by
          simpa [view, Machine.RoundView.boundedActive, hcutoff]
            using hlocal.1
        simp at hempty
      have havailable :
          EventGraph.FrontierAction.Available G h.lastState.state.1
            who frontierAction := by
        have hbounded := hlocal.2
        rw [Machine.RoundView.boundedAvailableActions] at hbounded
        rw [if_neg hnotCutoff] at hbounded
        have hfrontier :
            frontierAction ∈
              EventGraph.frontierAvailableActions
                G h.lastState.state who := by
          simpa [view, EventGraph.frontierRoundView] using hbounded
        simpa [EventGraph.frontierAvailableActions] using hfrontier
      rcases
          (EventGraph.FrontierAction.Available.value?_isSome_iff_readyCommitNode
            havailable).2 hready with
        ⟨value, hvalue⟩
      simp [hmove, hvalue] at hproject

/-- At an active frontier checkpoint for a replayed source commit, every
supported projection of the legal action law at the current node is a concrete
value. -/
theorem currentNodeValueLaw_support_some
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
    (hactive :
      who ∈
        Machine.RoundView.boundedActive
          (EventGraph.frontierRoundView
            (primitiveMachineSpec (compile program.core))
            presentation semantics)
          horizon h.lastState)
    {result :
      Option (L.Val (((compile program.core).graph.nodeRow node).ty))}
    (hresultSupport :
      result ∈
        (Math.ProbabilityMassFunction.pushforward
          (Machine.RoundView.legalActionLaw
            (EventGraph.frontierRoundView
              (primitiveMachineSpec (compile program.core))
              presentation semantics)
            horizon σ h hterm)
          (nodeValueProjection
            (primitiveMachineSpec (compile program.core))
            presentation semantics (who := who) node)).support) :
    ∃ value, result = some value := by
  let view :=
    EventGraph.frontierRoundView
      (primitiveMachineSpec (compile program.core))
      presentation semantics
  let project :
      Machine.RoundView.BoundedLegalAction view horizon h.lastState →
        Option (L.Val (((compile program.core).graph.nodeRow node).ty)) :=
    nodeValueProjection
      (primitiveMachineSpec (compile program.core))
      presentation semantics (who := who) node
  cases result with
  | none =>
      have hnoneSupport :
          none ∈
            (Math.ProbabilityMassFunction.pushforward
              (Machine.RoundView.legalActionLaw
                view horizon σ h hterm)
              project).support := by
        simpa [view, project] using hresultSupport
      exact False.elim
        (projected_nodeValueLaw_none_not_support_of_ready_active
          (G := (compile program.core).graph)
          (primitiveMachineSpec (compile program.core))
          presentation semantics σ h hterm
          (by simpa [view] using hactive)
          (currentNode_readyCommitNode_after_internalClosure
            program replay hnode fuel hsupport)
          (by simpa [view, project] using hnoneSupport))
  | some value =>
      exact ⟨value, rfl⟩

end Projected
end SourceFrontier
end ToEventGraph

end Vegas
