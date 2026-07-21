/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Projected
import Vegas.Frontier.RoundView.Bounded

/-!
# Frontier-induced source query strategies

This module turns the frontier legal-action law at a replayed source commit
into the source commit-value law.  The construction is the local strategic
bridge used by the full source/frontier profile translation:

1. project the frontier legal-action law to the current source-order node;
2. erase the impossible `none` branch, proved in `Projected`;
3. cast the node value back to the source commit type; and
4. attach the source guard proof, proved in `Query`.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Project an arbitrary distribution over legal frontier actions to the value
assigned to one source-order commit node. -/
noncomputable def nodeOptionLawOfActionDist
    (program : WFProgram P L)
    (presentation :
      EventGraph.CheckpointPresentation (compile program.core).graph)
    (semantics :
      EventGraph.FrontierRoundSemantics
        (primitiveMachineSpec (compile program.core)) presentation)
    {horizon : Nat}
    (h :
      Machine.RoundView.BoundedHistory
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics) horizon)
    (actionLaw :
      PMF
        (Machine.RoundView.BoundedLegalAction
          (EventGraph.frontierRoundView
            (primitiveMachineSpec (compile program.core))
            presentation semantics)
          horizon h.lastState))
    {who : P}
    (node : Fin (compile program.core).graph.nodeCount) :
    PMF (Option (L.Val (((compile program.core).graph.nodeRow node).ty))) :=
  Math.ProbabilityMassFunction.pushforward actionLaw
    (nodeValueProjection
      (primitiveMachineSpec (compile program.core))
      presentation semantics (who := who) node)

/-- At a replayed active source commit, any legal-action distribution projects
only concrete values at the current node. -/
theorem nodeOptionLawOfActionDist_support_some
    (program : WFProgram P L)
    (presentation :
      EventGraph.CheckpointPresentation (compile program.core).graph)
    (semantics :
      EventGraph.FrontierRoundSemantics
        (primitiveMachineSpec (compile program.core)) presentation)
    {horizon : Nat}
    (h :
      Machine.RoundView.BoundedHistory
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics) horizon)
    (actionLaw :
      PMF
        (Machine.RoundView.BoundedLegalAction
          (EventGraph.frontierRoundView
            (primitiveMachineSpec (compile program.core))
            presentation semantics)
          horizon h.lastState))
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
        (nodeOptionLawOfActionDist program presentation semantics
          h actionLaw (who := who) node).support) :
    ∃ value, result = some value := by
  cases result with
  | none =>
      exact False.elim
        (projected_nodeValue_none_not_support_of_ready_active
          (G := (compile program.core).graph)
          (primitiveMachineSpec (compile program.core))
          presentation semantics h actionLaw hactive
          (currentNode_readyCommitNode_after_internalClosure
            program replay hnode fuel hsupport)
          (by
            simpa [nodeOptionLawOfActionDist,
              nodeValueProjection] using hresultSupport))
  | some value =>
      exact ⟨value, rfl⟩

/-- A concrete value supported by an arbitrary legal-action distribution's
current-node projection is legal for the replayed source commit. -/
theorem sourceLegal_of_nodeOptionLawOfActionDist_support
    (program : WFProgram P L)
    (presentation :
      EventGraph.CheckpointPresentation (compile program.core).graph)
    (semantics :
      EventGraph.FrontierRoundSemantics
        (primitiveMachineSpec (compile program.core)) presentation)
    {horizon : Nat}
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
    (actionLaw :
      PMF
        (Machine.RoundView.BoundedLegalAction
          (EventGraph.frontierRoundView
            (primitiveMachineSpec (compile program.core))
            presentation semantics)
          horizon h.lastState))
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
        (nodeOptionLawOfActionDist program presentation semantics
          h actionLaw (who := who) node).support) :
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
    nodeValueProjection
      (primitiveMachineSpec (compile program.core))
      presentation semantics (who := who) node
  have hvalueSupport' :
      some value ∈
        (Math.ProbabilityMassFunction.pushforward
          actionLaw project).support := by
    simpa [nodeOptionLawOfActionDist, compiled, view, project]
      using hvalueSupport
  rw [Math.ProbabilityMassFunction.pushforward] at hvalueSupport'
  rcases (PMF.mem_support_map_iff project actionLaw
      (some value)).mp hvalueSupport' with
    ⟨action, _hactionSupport, hproject⟩
  dsimp [project, nodeValueProjection] at hproject
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

/-- Source commit-value law induced by an arbitrary distribution over legal
frontier actions at the corresponding frontier checkpoint. -/
noncomputable def sourceCommitValueLawOfActionDist
    (program : WFProgram P L)
    (presentation :
      EventGraph.CheckpointPresentation (compile program.core).graph)
    (semantics :
      EventGraph.FrontierRoundSemantics
        (primitiveMachineSpec (compile program.core)) presentation)
    {horizon : Nat}
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
    (actionLaw :
      PMF
        (Machine.RoundView.BoundedLegalAction
          (EventGraph.frontierRoundView
            (primitiveMachineSpec (compile program.core))
            presentation semantics)
          horizon h.lastState))
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
          horizon h.lastState) :
    PMF
      { value : L.Val b //
        evalGuard (Player := P) (L := L) guard value
          ((env.toView who).eraseEnv) = true } := by
  let optionLaw :=
    nodeOptionLawOfActionDist program presentation semantics
      h actionLaw (who := who) node
  let htotal :
      ∀ result ∈ optionLaw.support,
        ∃ value, result = some value :=
    fun result hresult =>
      nodeOptionLawOfActionDist_support_some
        program presentation semantics h actionLaw replay hnode fuel
        hsupport hactive hresult
  let valueLaw := eraseNonePMF optionLaw htotal
  exact
    valueLaw.bindOnSupport fun value hvalueSupport =>
      let sourceValue : L.Val b :=
        cast
          (congrArg L.Val
            (currentNodeType program replay hnode))
          value
      have hsomeSupport :
          some value ∈ optionLaw.support := by
        exact
          (mem_support_eraseNonePMF_iff
            (dist := optionLaw) (htotal := htotal)).mp hvalueSupport
      have hguard :
          evalGuard (Player := P) (L := L) guard sourceValue
            ((env.toView who).eraseEnv) = true := by
        simpa [sourceValue] using
          sourceLegal_of_nodeOptionLawOfActionDist_support
            program presentation semantics h hterm actionLaw replay hnode fuel
            hsupport value
            (by simpa [optionLaw] using hsomeSupport)
      PMF.pure ⟨sourceValue, hguard⟩

/-- Source commit-value law induced by conditioning the current legal frontier
action law on an arbitrary finite observation of the legal action.

This is the reusable source-order serialization step for the interior of a
simultaneous frontier round: earlier source queries condition the frontier
legal-action law to a fiber, and the next source query is read from that fiber. -/
noncomputable def conditionedSourceCommitValueLaw
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
    {β : Type} [Finite β]
    (conditionProject :
      Machine.RoundView.BoundedLegalAction
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics)
        horizon h.lastState → β)
    (conditionValue : β)
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
          horizon h.lastState) :
    PMF
      { value : L.Val b //
        evalGuard (Player := P) (L := L) guard value
          ((env.toView who).eraseEnv) = true } :=
  sourceCommitValueLawOfActionDist
    program presentation semantics h hterm
    (Math.ProbabilityMassFunction.condOn
      (Machine.RoundView.legalActionLaw
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics)
        horizon σ h hterm)
      conditionProject conditionValue)
    replay hnode fuel hsupport hactive

/-- Conditioned source commit-value law for the common case where the
conditioning fiber is a previously serialized source-order commit node. -/
noncomputable def conditionedNodeSourceCommitValueLaw
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
    {prevWho : P}
    (prevNode : Fin (compile program.core).graph.nodeCount)
    [Finite
      (Option
        (L.Val (((compile program.core).graph.nodeRow prevNode).ty)))]
    (prevValue :
      Option
        (L.Val (((compile program.core).graph.nodeRow prevNode).ty)))
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
          horizon h.lastState) :
    PMF
      { value : L.Val b //
        evalGuard (Player := P) (L := L) guard value
          ((env.toView who).eraseEnv) = true } :=
  conditionedSourceCommitValueLaw
    program presentation semantics σ h hterm
    (nodeValueProjection
      (primitiveMachineSpec (compile program.core))
      presentation semantics (who := prevWho) prevNode)
    prevValue
    replay hnode fuel hsupport hactive

/-- The option-valued frontier law obtained by observing one source-order commit
node in the current legal frontier action law. -/
noncomputable def currentNodeOptionLaw
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
    {who : P}
    (node : Fin (compile program.core).graph.nodeCount) :
    PMF (Option (L.Val (((compile program.core).graph.nodeRow node).ty))) :=
  nodeOptionLawOfActionDist program presentation semantics h
    (Machine.RoundView.legalActionLaw
      (EventGraph.frontierRoundView
        (primitiveMachineSpec (compile program.core))
        presentation semantics)
      horizon σ h hterm)
    (who := who) node

/-- At a replayed source commit, the current-node frontier projection is total:
all supported option results are `some`. -/
theorem currentNodeOptionLaw_support_some
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
        (currentNodeOptionLaw program presentation semantics
          σ h hterm (who := who) node).support) :
    ∃ value, result = some value := by
  exact
    nodeOptionLawOfActionDist_support_some
      program presentation semantics h
      (Machine.RoundView.legalActionLaw
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics)
        horizon σ h hterm)
      replay hnode fuel hsupport hactive
      (by
        simpa [currentNodeOptionLaw] using hresultSupport)

/-- A supported concrete value from `currentNodeOptionLaw` is source-legal for
the replayed source commit. -/
theorem sourceLegal_of_currentNodeOptionLaw_support
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
        (currentNodeOptionLaw program presentation semantics
          σ h hterm (who := who) node).support) :
    let sourceValue : L.Val b :=
      cast
        (congrArg L.Val
          (currentNodeType program replay hnode))
        value
    evalGuard (Player := P) (L := L) guard sourceValue
      ((env.toView who).eraseEnv) = true := by
  exact
    sourceLegal_of_nodeOptionLawOfActionDist_support
      program presentation semantics h hterm
      (Machine.RoundView.legalActionLaw
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics)
        horizon σ h hterm)
      replay hnode fuel hsupport value
      (by simpa [currentNodeOptionLaw] using hvalueSupport)

/-- Frontier-induced source commit-value law at a replayed source commit.

The resulting PMF lives directly over source-legal commit values.  It is the
local ingredient needed to define a source strategy from a frontier behavioral
profile at reachable source query points. -/
noncomputable def currentSourceCommitValueLaw
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
          horizon h.lastState) :
    PMF
      { value : L.Val b //
        evalGuard (Player := P) (L := L) guard value
          ((env.toView who).eraseEnv) = true } := by
  exact
    sourceCommitValueLawOfActionDist
      program presentation semantics h hterm
      (Machine.RoundView.legalActionLaw
        (EventGraph.frontierRoundView
          (primitiveMachineSpec (compile program.core))
          presentation semantics)
        horizon σ h hterm)
      replay hnode fuel hsupport hactive

end ToEventGraph

end Vegas
