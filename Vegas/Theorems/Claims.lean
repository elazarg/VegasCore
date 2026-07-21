/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Theorems.Graph
import Vegas.Theorems.Execution
import Vegas.Theorems.Progress
import Vegas.Theorems.Visibility
import Vegas.Theorems.Outcome
import Vegas.Theorems.Strategy
import Vegas.Theorems.Kuhn
import Vegas.Theorems.FOSG
import Vegas.Theorems.EFG
import Vegas.Theorems.Refinement
import Vegas.Theorems.RuntimeSolutionConcepts
import Vegas.Frontier.SourceStrategicAdequacy

/-!
# Paper-facing theorem index

This module states the main paper-facing claims proved by the theorem modules.
The lower theorem modules contain the detailed proof surfaces; this file keeps
the end-to-end story visible:

* checked programs compile to well-formed event graphs;
* checked guard legality gives graph/checkpoint progress;
* compiled outcomes agree with source payoffs;
* frontier/FOSG denotations preserve utility distributions;
* Kuhn realization connects behavioral play to product mixed pure play;
* runtime refinements preserve strategic utility distributions once supplied
  with an adequate strategy-indexed runtime law family.
-/

namespace Vegas

namespace WFProgram

open GameTheory
open ToEventGraph

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

omit [Fintype P] in
/-- Checked programs compile to well-formed source-free event graphs. -/
theorem claim_compiles_to_wellFormed_eventGraph
    (program : WFProgram P L) :
    (ToEventGraph.compile program.core).graph.WF :=
  program.compiledGraph_wf

omit [Fintype P] in
/-- Checked guard legality supplies progress for the primitive downset
checkpoint model. -/
theorem claim_checked_program_has_checkpoint_progress
    (program : WFProgram P L)
    {state : (ToEventGraph.primitiveDownsetCheckpointModel program).State}
    (hterminal :
      ¬ (ToEventGraph.primitiveDownsetCheckpointModel program).terminal
        state) :
    ∃ dst,
      (ToEventGraph.primitiveDownsetCheckpointModel program).allowed
        state dst :=
  program.primitiveDownsetCheckpoint_progress hterminal

/-- Scoped schedule-confluence package for the checked program's compiled
graph and canonical frontier round model. It includes full-schedule confluence
to canonical completion and the checkpoint-history well-definedness facts the
frontier uses. -/
theorem claim_schedule_confluence_frontier_round_wellDefined
    (program : WFProgram P L) [FiniteDomains program] :
    program.ScheduleConfluenceFrontierRoundWellDefined :=
  program.compiledGraph_scheduleConfluence_frontierRound_wellDefined

omit [Fintype P] in
/-- Source order is faithfully compiled at the graph-owner level: canonical
graph node owners are the source order trace projected to graph node owners. -/
theorem claim_compiled_graph_node_order_reflects_source_order
    (program : WFProgram P L) (who : P) :
    (((ToEventGraph.compile program.core).graph.nodeOrder.map
        fun node => ((ToEventGraph.compile program.core).graph.nodeRow node).owner)) =
      (program.core.prog.orderTrace who).map
        SourcePlayerEvent.Kind.graphOwner :=
  program.compiledGraph_nodeOrder_owners_eq_sourceOrderTrace_graphOwners who

omit [Fintype P] in
/-- Source order is faithfully compiled at the per-player readable-output
level: the compiled graph's readable-owner order is the source order trace's
graph-owner projection restricted to values readable by the player. -/
theorem claim_compiled_graph_readable_order_reflects_source_order
    (program : WFProgram P L) (who : P) :
    ((((ToEventGraph.compile program.core).graph.readableOrder who
        (ToEventGraph.compile program.core).graph.nodeOrder).map
        fun node => ((ToEventGraph.compile program.core).graph.nodeRow node).owner)) =
      ((program.core.prog.orderTrace who).map
        SourcePlayerEvent.Kind.graphOwner).filter
          fun owner => decide (owner = none ∨ owner = some who) :=
  program.compiledGraph_readableOrder_owners_eq_sourceOrderTrace_readableGraphOwners
    who

omit [Fintype P] in
/-- The flat primitive-linearization readable-order theorem remains explicitly
fenced: under a readability fence, any two dependency-respecting full orders
present the same readable-output order to the player. -/
theorem claim_compiled_graph_readable_order_eq_of_fence
    (program : WFProgram P L)
    {who : P}
    {left right :
      List (Fin (ToEventGraph.compile program.core).graph.nodeCount)}
    (hleft :
      (ToEventGraph.compile program.core).graph.IsTopo left)
    (hright :
      (ToEventGraph.compile program.core).graph.IsTopo right)
    (hfence :
      (ToEventGraph.compile program.core).graph.Fence who) :
    (ToEventGraph.compile program.core).graph.readableOrder who left =
      (ToEventGraph.compile program.core).graph.readableOrder who right :=
  program.compiledGraph_readableOrder_eq_of_fence hleft hright hfence

omit [Fintype P] in
/-- Primitive-machine terminal outcomes agree with the source payoff
projection reconstructed from the terminal compiled graph store. -/
theorem claim_terminal_outcome_is_source_payoff
    (program : WFProgram P L)
    (state :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State)
    (hterminal :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).terminal state) :
    (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).outcome state =
      some (ToEventGraph.sourceOutcomeAtTerminal program.core state
        (by
          exact hterminal)) :=
  ToEventGraph.primitiveOutcome_eq_sourceAtTerminal
    program.core state hterminal

/-- The pure completed-frontier outcome kernel is exactly the canonical run
distribution pushed through the checked program's source payoff projection. -/
theorem claim_pure_frontier_outcome_kernel_is_source_projection
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.frontierSemantics.pure.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.pure.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          ((program.frontierSemantics.pure.view).legalPureToBehavioral
            (ToEventGraph.completionBound
              (ToEventGraph.compile program.core)) profile)) :=
  program.pureFrontierOutcomeKernel_sourceMap profile

/-- The behavioral completed-frontier outcome kernel is exactly the canonical
run distribution pushed through the checked program's source payoff
projection. -/
theorem claim_behavioral_frontier_outcome_kernel_is_source_projection
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierSemantics.behavioral.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.behavioral.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core)) profile) :=
    program.behavioralFrontierOutcomeKernel_sourceMap profile

omit [Fintype P] in
/-- Every source-native strategic history prefix replays into a reachable
compiled graph prefix in canonical source order.  The replay certificate keeps
the compiler dictionary for the current source continuation, so the graph store
agrees with the current source environment before terminal payoff projection. -/
theorem claim_source_strategic_prefix_replays_to_compiled_graph
    (program : WFProgram P L)
    (state :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core)) :
    Nonempty
      (ToEventGraph.SourcePrefixReplay program.core
        state.history.current) :=
  program.sourceStrategicHistory_prefixReplay state

omit [Fintype P] in
/-- At a replayed source `commit` prefix, the next source-order compiled graph
node is ready as a commit node for the same player.  This is the concrete
menu-domain fact used by raw source/frontier strategy translation. -/
theorem claim_source_prefix_commit_is_ready_compiled_commit
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L)) :
    ∃ node : Fin (ToEventGraph.buildResult program.core).graph.nodeCount,
      (node : Nat) = replay.compilerState.nodes.length ∧
      EventGraph.ReadyCommitNode
        (ToEventGraph.buildResult program.core).graph
        replay.state.1 who node :=
  ToEventGraph.SourcePrefixReplay.readyCommitNode program.core replay

omit [Fintype P] in
/-- At a replayed source `commit` prefix, the current source-order compiled
node's frontier value type is exactly the source commit value type. -/
theorem claim_source_prefix_commit_current_node_type
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (ToEventGraph.compile program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length) :
    (((ToEventGraph.compile program.core).graph.nodeRow node).ty) = b :=
  ToEventGraph.SourcePrefixReplay.currentCommitNode_ty_eq
    program.core replay hnode

omit [Fintype P] in
/-- At a replayed source `commit` prefix, every source-legal commit value is
available as the corresponding compiled graph commit action. -/
theorem claim_source_prefix_commit_source_legal_value_available
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    (value : L.Val b)
    (hguard :
      evalGuard (Player := P) (L := L) guard value
        ((env.toView who).eraseEnv) = true) :
    ∃ node : Fin (ToEventGraph.buildResult program.core).graph.nodeCount,
      (node : Nat) = replay.compilerState.nodes.length ∧
      EventGraph.CommitAvailable
        (ToEventGraph.buildResult program.core).graph replay.state.1 who
        { node := node, value := { ty := b, value := value } } :=
  ToEventGraph.SourcePrefixReplay.commitAvailable_of_source_guard
    program.core replay value hguard

omit [Fintype P] in
/-- At a replayed source `commit` prefix, availability of the current
source-order compiled commit action reflects back to source guard legality. -/
theorem claim_source_prefix_commit_available_value_source_legal
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (ToEventGraph.buildResult program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length)
    (value : L.Val b)
    (havailable :
      EventGraph.CommitAvailable
        (ToEventGraph.buildResult program.core).graph replay.state.1 who
        { node := node, value := { ty := b, value := value } }) :
    evalGuard (Player := P) (L := L) guard value
      ((env.toView who).eraseEnv) = true :=
  ToEventGraph.SourcePrefixReplay.source_guard_of_commitAvailable
    program.core replay hnode value havailable

omit [Fintype P] in
/-- At a replayed source `commit` prefix, source commit-menu membership is
equivalent to availability of the corresponding current source-order compiled
commit action. -/
theorem claim_source_prefix_commit_menu_iff_compiled_available
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (ToEventGraph.buildResult program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length)
    (value : L.Val b) :
    value ∈ SourceCommitMenu (L := L) who guard env ↔
      EventGraph.CommitAvailable
        (ToEventGraph.buildResult program.core).graph replay.state.1 who
        { node := node, value := { ty := b, value := value } } :=
  ToEventGraph.SourcePrefixReplay.sourceCommitMenu_iff_commitAvailable
    program.core replay hnode value

omit [Fintype P] in
/-- Compiled commit availability survives frontier internal closure.  This is
the scheduling bridge needed because canonical frontier checkpoints close ready
internal graph work before querying strategic commit actions. -/
theorem claim_compiled_commit_available_persists_through_internal_closure
    (program : WFProgram P L)
    (fuel : Nat)
    {state dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State}
    {who : P}
    {action :
      EventGraph.CommitAction
        (ToEventGraph.compile program.core).graph who}
    (havailable :
      EventGraph.CommitAvailable
        (ToEventGraph.compile program.core).graph state.1 who action)
    (hsupport :
      dst ∈
        (ToEventGraph.internalClosureTransition
          (ToEventGraph.compile program.core) fuel state).support) :
    EventGraph.CommitAvailable
      (ToEventGraph.compile program.core).graph dst.1 who action :=
  ToEventGraph.commitAvailable_persist_after_internalClosureTransition_support
    (ToEventGraph.compile program.core) fuel havailable hsupport

omit [Fintype P] in
/-- Compiled commit availability after frontier internal closure reflects back
to the pre-closure state when the commit node was already ready there. -/
theorem claim_compiled_commit_available_reflects_before_internal_closure
    (program : WFProgram P L)
    (fuel : Nat)
    {state dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State}
    {who : P}
    {action :
      EventGraph.CommitAction
        (ToEventGraph.compile program.core).graph who}
    (hready :
      EventGraph.Ready
        (ToEventGraph.compile program.core).graph state.1 action.node)
    (hsupport :
      dst ∈
        (ToEventGraph.internalClosureTransition
          (ToEventGraph.compile program.core) fuel state).support)
    (havailable :
      EventGraph.CommitAvailable
        (ToEventGraph.compile program.core).graph dst.1 who action) :
    EventGraph.CommitAvailable
      (ToEventGraph.compile program.core).graph state.1 who action :=
  ToEventGraph.commitAvailable_reflect_before_internalClosureTransition_support
    (ToEventGraph.compile program.core) fuel hready hsupport havailable

omit [Fintype P] in
/-- A source-legal value for the current replayed source `commit` remains a
compiled-available commit action after any supported frontier internal closure
from that replay state. -/
theorem claim_source_prefix_commit_source_legal_value_available_after_internal_closure
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (ToEventGraph.compile program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length)
    (value : L.Val b)
    (hguard :
      evalGuard (Player := P) (L := L) guard value
        ((env.toView who).eraseEnv) = true)
    (fuel : Nat)
    {dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State}
    (hsupport :
      dst ∈
        (ToEventGraph.internalClosureTransition
          (ToEventGraph.compile program.core) fuel replay.state).support) :
    EventGraph.CommitAvailable
      (ToEventGraph.compile program.core).graph dst.1 who
      { node := node, value := { ty := b, value := value } } := by
  have havailable₀ :
      EventGraph.CommitAvailable
        (ToEventGraph.compile program.core).graph replay.state.1 who
        { node := node, value := { ty := b, value := value } } := by
    exact
      (ToEventGraph.SourcePrefixReplay.sourceCommitMenu_iff_commitAvailable
        program.core replay hnode value).mp hguard
  exact
    ToEventGraph.commitAvailable_persist_after_internalClosureTransition_support
      (ToEventGraph.compile program.core) fuel havailable₀ hsupport

omit [Fintype P] in
/-- Availability of the current replayed source-order commit action after
frontier internal closure reflects back to source guard legality before that
closure. -/
theorem claim_source_prefix_commit_available_after_internal_closure_value_source_legal
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (ToEventGraph.compile program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length)
    (value : L.Val b)
    (fuel : Nat)
    {dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State}
    (hsupport :
      dst ∈
        (ToEventGraph.internalClosureTransition
          (ToEventGraph.compile program.core) fuel replay.state).support)
    (havailable :
      EventGraph.CommitAvailable
        (ToEventGraph.compile program.core).graph dst.1 who
        { node := node, value := { ty := b, value := value } }) :
    evalGuard (Player := P) (L := L) guard value
      ((env.toView who).eraseEnv) = true := by
  rcases
      ToEventGraph.SourcePrefixReplay.readyCommitNode
        program.core replay with
    ⟨currentNode, hcurrentNode, hreadyCommit⟩
  have hnodeEq : currentNode = node := by
    exact Fin.ext (hcurrentNode.trans hnode.symm)
  subst currentNode
  have hready :
      EventGraph.Ready
        (ToEventGraph.compile program.core).graph replay.state.1 node :=
    hreadyCommit.ready
  have hbefore :
      EventGraph.CommitAvailable
        (ToEventGraph.compile program.core).graph replay.state.1 who
        { node := node, value := { ty := b, value := value } } :=
    ToEventGraph.commitAvailable_reflect_before_internalClosureTransition_support
      (ToEventGraph.compile program.core) fuel hready hsupport havailable
  exact
    ToEventGraph.SourcePrefixReplay.source_guard_of_commitAvailable
      program.core replay hnode value hbefore

omit [Fintype P] in
/-- At a replayed source `commit` prefix, source commit-menu membership is
equivalent to availability of the corresponding current source-order compiled
commit action after any supported frontier internal closure from that prefix. -/
theorem claim_source_prefix_commit_menu_iff_available_after_internal_closure
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (ToEventGraph.compile program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length)
    (value : L.Val b)
    (fuel : Nat)
    {dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State}
    (hsupport :
      dst ∈
        (ToEventGraph.internalClosureTransition
          (ToEventGraph.compile program.core) fuel replay.state).support) :
    value ∈ SourceCommitMenu (L := L) who guard env ↔
      EventGraph.CommitAvailable
        (ToEventGraph.compile program.core).graph dst.1 who
        { node := node, value := { ty := b, value := value } } := by
  constructor
  · intro hmenu
    exact
      claim_source_prefix_commit_source_legal_value_available_after_internal_closure
        program replay hnode value hmenu fuel hsupport
  · intro havailable
    exact
      claim_source_prefix_commit_available_after_internal_closure_value_source_legal
        program replay hnode value fuel hsupport havailable

omit [Fintype P] in
/-- If an available frontier local action after internal closure assigns a
value to the current replayed source-order commit node, that node value
satisfies the source guard after casting along the compiler's current-node type
equality. -/
theorem claim_frontier_action_current_value_source_legal_after_internal_closure
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (ToEventGraph.compile program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length)
    (fuel : Nat)
    {dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State}
    (hsupport :
      dst ∈
        (ToEventGraph.internalClosureTransition
          (ToEventGraph.compile program.core) fuel replay.state).support)
    (frontierAction :
      EventGraph.FrontierAction
        (ToEventGraph.compile program.core).graph who)
    (hfrontierAvailable :
      EventGraph.FrontierAction.Available
        (ToEventGraph.compile program.core).graph dst.1 who
        frontierAction)
    (value :
      L.Val (((ToEventGraph.compile program.core).graph.nodeRow node).ty))
    (hvalue : frontierAction.value? node = some value) :
    let sourceValue : L.Val b :=
      cast
        (congrArg L.Val
          (claim_source_prefix_commit_current_node_type
            program replay hnode))
        value
    evalGuard (Player := P) (L := L) guard sourceValue
      ((env.toView who).eraseEnv) = true := by
  let hty :=
    claim_source_prefix_commit_current_node_type program replay hnode
  let sourceValue : L.Val b := cast (congrArg L.Val hty) value
  have hcommitNode :
      EventGraph.CommitAvailable
        (ToEventGraph.compile program.core).graph dst.1 who
        { node := node,
          value :=
            (ToEventGraph.compile program.core).graph.nodeTypedValue
              node value } :=
    hfrontierAvailable.commitAvailable_of_value hvalue
  have htyped :
      (ToEventGraph.compile program.core).graph.nodeTypedValue node value =
        ({ ty := b, value := sourceValue } :
          EventGraph.TypedValue L) := by
    cases hty
    rfl
  have hcommit :
      EventGraph.CommitAvailable
        (ToEventGraph.compile program.core).graph dst.1 who
        { node := node, value := { ty := b, value := sourceValue } } := by
    simpa [htyped] using hcommitNode
  exact
    claim_source_prefix_commit_available_after_internal_closure_value_source_legal
      program replay hnode sourceValue fuel hsupport hcommit

omit [Fintype P] in
/-- A source-legal current commit value can be extended to a full available
frontier local action after internal closure.  Other ready commit nodes are
filled by the canonical live frontier action. -/
theorem claim_source_legal_value_extends_to_available_frontier_action_after_internal_closure
    (program : WFProgram P L)
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core
        ({ ctx := Γ, env := env,
           cont := VegasCore.commit x who guard tail } :
          SourceConfig P L))
    {node : Fin (ToEventGraph.compile program.core).graph.nodeCount}
    (hnode : (node : Nat) = replay.compilerState.nodes.length)
    (value : L.Val b)
    (hguard :
      evalGuard (Player := P) (L := L) guard value
        ((env.toView who).eraseEnv) = true)
    (fuel : Nat)
    {dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State}
    (hsupport :
      dst ∈
        (ToEventGraph.internalClosureTransition
          (ToEventGraph.compile program.core) fuel replay.state).support) :
    ∃ frontierAction :
        EventGraph.FrontierAction
          (ToEventGraph.compile program.core).graph who,
      EventGraph.FrontierAction.Available
          (ToEventGraph.compile program.core).graph dst.1 who
          frontierAction ∧
        frontierAction.value? node =
          some
            (cast
              (congrArg L.Val
                (claim_source_prefix_commit_current_node_type
                  program replay hnode).symm)
              value) := by
  exact
    sourceLegal_extends_to_available_frontierAction_after_internalClosure
      program replay hnode value hguard fuel hsupport

omit [Fintype P] in
/-- Terminal outcomes of the source-native strategic game replay into a
reachable terminal compiled graph state whose store reconstructs the source
environment. -/
theorem claim_source_strategic_terminal_history_replays_to_compiled_graph
    (program : WFProgram P L)
    (horizon : Nat) (cutoff : Payoff P)
    (profile : (program.sourceStrategicGame horizon cutoff).Profile)
    {state :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core)}
    (hsupport :
      state ∈
        ((program.sourceStrategicGame horizon cutoff).outcomeKernel
          profile).support)
    (hterminal : state.history.current.IsTerminal) :
    let result := ToEventGraph.buildResult program.core
    ∃ cfg : EventGraph.ReachableConfig result.graph,
      EventGraph.Terminal result.graph cfg.1 ∧
      ToEventGraph.StoreReconstructs program.core cfg.1.store
        state.history.current :=
  program.sourceStrategicGame_support_reachableConfig
    horizon cutoff profile hsupport hterminal

/-- Supported behavioral frontier histories replay back to terminal source
runs in source order, reconstructing the source environment from the same
compiled store. -/
theorem claim_behavioral_frontier_history_replays_to_source_run
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile)
    {history : program.BehavioralFrontierHistory}
    (hsupport :
      history ∈
        (program.frontierSemantics.behavioralHistoryKernel
          profile).support) :
    ∃ labels : List (Label P L),
      ∃ final : SourceConfig P L,
        SourceConfig.LabeledStar
          (ToEventGraph.sourceStart program.core) labels final ∧
        final.IsTerminal ∧
        ToEventGraph.StoreReconstructs program.core
          history.lastState.state.1.store final :=
  program.frontierSemantics.behavioralHistory_support_sourceRun
    profile hsupport

/-- The checkpoint-aligned source behavioral game has the same observed
outcome law as the completed behavioral frontier game, when frontier outcomes
are observed through `some`. -/
theorem claim_source_checkpoint_behavioral_kernel_matches_frontier
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.sourceCheckpointBehavioralGame.Profile) :
    program.sourceCheckpointBehavioralGame.outcomeKernel profile =
      PMF.map some
        (program.behavioralFrontierGame.outcomeKernel profile) :=
  program.sourceCheckpointBehavioralGame_outcomeKernel_eq_map_some profile

/-- The checkpoint-aligned source behavioral game and the completed behavioral
frontier game are related by a two-way Nash-deviation bisimulation. -/
noncomputable def
    claim_source_checkpoint_behavioral_frontier_deviation_bisimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationBisimulation
      program.sourceCheckpointBehavioralGame program.behavioralFrontierGame
      (Option (Outcome P)) :=
  program.sourceCheckpointBehavioralFrontierNashDeviationBisimulation

/-- The payoff-facing FOSG denotation and the native behavioral frontier game
have the same joint utility distribution. -/
theorem claim_fosg_utility_distribution_adequacy
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      program.behavioralFrontierGame.udist profile :=
  program.frontierFOSG_payoff_udist_behavioral profile

/-- The payoff-facing serialized EFG denotation has the checked program's
source payoff utility law after translating native behavioral frontier
profiles through the FOSG/EFG bridge. -/
theorem claim_efg_utility_distribution_adequacy
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            profile).extend) =
      program.behavioralFrontierGame.udist profile :=
  Theorems.EFG.WFProgram.frontier_plain_efg_payoff_udist_behavioral
    program profile

/-- Behavioral frontier profiles induce product mixed pure frontier profiles
with the same joint utility distribution. -/
theorem claim_kuhn_behavioral_to_mixedPure_udist
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure profile) =
      program.behavioralFrontierGame.udist profile :=
  program.mixedPureFrontier_udist_of_behavioral profile

/-- The canonical mixed-pure/behavioral Kuhn bridge is a standard two-way Nash
deviation bisimulation, so its strategic transport content uses the generic
GameTheory relation. -/
noncomputable def claim_kuhn_mixed_pure_behavioral_deviation_bisimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationBisimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.mixedPureBehavioralFrontier_deviationBisimulation

/-- The Kuhn bridge is stated over the canonical frontier `RoundView`
information model.  Its information states are player event histories, and
the checked program supplies observable menus for that model. -/
theorem claim_kuhn_uses_canonical_roundView_information
    (program : WFProgram P L) [FiniteDomains program] :
    program.frontierSemantics.games.view.MenusObservable
      program.frontierSemantics.horizon :=
  program.frontierSemantics.menus

/-- Behavioral frontier strategies are local to canonical `RoundView` player
views: histories with the same player view induce the same strategy
distribution. -/
theorem claim_behavioral_strategies_are_roundView_local
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.BehavioralFrontierStrategy player)
    {left right : program.BehavioralFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    strategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player left) =
      strategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player right) :=
  program.behavioralFrontierStrategy_eq_of_playerView_eq strategy hview

omit [Fintype P] in
/-- A `ValueCodec` gives the first non-wrapper runtime rung below the
primitive compiled machine: codec states carry wire-encoded graph stores and
refine the primitive machine by erasing the wire layer. -/
noncomputable def claim_value_codec_refines_primitive_machine
    (program : WFProgram P L)
    (valueCodec : Runtime.ValueCodec L) :
    Machine.StochasticRefinement
      (valueCodec.codecMachine
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core)))
      (EventGraph.ToMachine.primitiveMachine
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core))) :=
  Runtime.ValueCodec.refinement valueCodec
    (ToEventGraph.primitiveMachineSpec
      (ToEventGraph.compile program.core))

omit [Fintype P] in
/-- Primitive event-batch law families lift through the codec refinement, so
strategy-indexed primitive schedulers can be run by the codec machine without
changing their projected trace law. -/
noncomputable def claim_value_codec_lifts_event_batch_law_family
    (program : WFProgram P L)
    (valueCodec : Runtime.ValueCodec L)
    {Strategy : P → Type}
    (family :
      (EventGraph.ToMachine.primitiveMachine
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core))).EventBatchLawFamily Strategy) :
    (Runtime.ValueCodec.refinement valueCodec
      (ToEventGraph.primitiveMachineSpec
        (ToEventGraph.compile program.core))).EventBatchLawFamilyLift
        Strategy family :=
  Runtime.ValueCodec.liftEventBatchLawFamily valueCodec
    (ToEventGraph.primitiveMachineSpec
      (ToEventGraph.compile program.core)) family

/-- A trace-adequate primitive law becomes a trace-adequate codec runtime law
for any frontier trace-game surface. -/
noncomputable def claim_value_codec_runtime_trace_adequacy
    (program : WFProgram P L) [FiniteDomains program]
    {surface : TraceGameSurface program}
    (valueCodec : Runtime.ValueCodec L)
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      (Runtime.ValueCodec.refinement valueCodec
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core))) :=
  RuntimeTraceAdequacy.codec valueCodec law

omit [Fintype P] in
/-- The message-in-flight wrapper refines the primitive compiled machine by
forgetting pending/delivered message buffers and erasing send/deliver events. -/
noncomputable def claim_message_in_flight_refines_primitive_machine
    (program : WFProgram P L)
    (Message : P → Type) :
    Machine.StochasticRefinement
      (Machine.messageInFlight
        (EventGraph.ToMachine.primitiveMachine
          (ToEventGraph.primitiveMachineSpec
            (ToEventGraph.compile program.core))) Message)
      (EventGraph.ToMachine.primitiveMachine
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core))) :=
  Machine.messageInFlight.refinement
    (EventGraph.ToMachine.primitiveMachine
      (ToEventGraph.primitiveMachineSpec
        (ToEventGraph.compile program.core))) Message

/-- A trace-adequate primitive law becomes a trace-adequate
message-in-flight runtime law by draining pending messages before each lifted
primitive event batch. -/
noncomputable def claim_message_in_flight_runtime_trace_adequacy
    (program : WFProgram P L) [FiniteDomains program]
    {surface : TraceGameSurface program}
    (Message : P → Type)
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      (Machine.messageInFlight.refinement
        (EventGraph.ToMachine.primitiveMachine
          (ToEventGraph.primitiveMachineSpec
            (ToEventGraph.compile program.core))) Message) :=
  RuntimeTraceAdequacy.messageInFlight Message law

/-- The first composed backend rung: codec wire storage plus a
message-in-flight layer still realizes any trace-adequate frontier surface. -/
noncomputable def claim_value_codec_message_in_flight_runtime_trace_adequacy
    (program : WFProgram P L) [FiniteDomains program]
    {surface : TraceGameSurface program}
    (valueCodec : Runtime.ValueCodec L)
    (Message : P → Type)
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      ((Runtime.ValueCodec.refinement valueCodec
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core))).compose
        (Machine.messageInFlight.refinement
          (valueCodec.codecMachine
            (ToEventGraph.primitiveMachineSpec
              (ToEventGraph.compile program.core))) Message)) :=
  RuntimeTraceAdequacy.codecMessageInFlight valueCodec Message law

/-- Runtime refinements preserve the checked behavioral frontier utility
distribution once the runtime supplies an adequate strategy-indexed event-batch
law family. -/
theorem claim_runtime_refinement_preserves_behavioral_udist
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R)
    (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.udist profile =
      program.behavioralFrontierGame.udist profile :=
  by
    simpa [behavioralFrontierTraceSurface] using
      bridge.implTraceGame_udist_surface profile

/-- Runtime refinements preserve the checked pure frontier utility
distribution once supplied with an adequate strategy-indexed event-batch law
family. This is the finite pure-strategy solver surface. -/
theorem claim_runtime_refinement_preserves_pure_udist
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R)
    (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.udist profile =
      program.pureFrontierGame.udist profile :=
  by
    simpa [pureFrontierTraceSurface] using
      bridge.implTraceGame_udist_surface profile

/-- Runtime refinements preserve the checked product mixed-pure frontier
utility distribution once supplied with an adequate strategy-indexed
event-batch law family. -/
theorem claim_runtime_refinement_preserves_mixed_pure_udist
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (mixedPureFrontierTraceSurface program) R)
    (profile : program.MixedPureFrontierProfile) :
    bridge.implTraceGame.udist profile =
      program.mixedPureFrontierGame.udist profile :=
  by
    simpa [mixedPureFrontierTraceSurface] using
      bridge.implTraceGame_udist_surface profile

/-- Runtime refinements preserve the payoff-vector law induced by correlated
behavioral frontier profile distributions. -/
theorem claim_runtime_refinement_preserves_behavioral_correlated_utility_law
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R)
    (profileLaw : program.BehavioralFrontierCorrelatedProfile) :
    correlatedUtilityLaw bridge.implTraceGame profileLaw =
      correlatedUtilityLaw program.behavioralFrontierGame profileLaw :=
  by
    simpa [behavioralFrontierTraceSurface] using
      bridge.implTraceGame_correlatedUtilityLaw_surface profileLaw

/-- Runtime refinements preserve the payoff-vector law induced by correlated
pure frontier profile distributions. -/
theorem claim_runtime_refinement_preserves_pure_correlated_utility_law
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R)
    (profileLaw : program.PureFrontierCorrelatedProfile) :
    correlatedUtilityLaw bridge.implTraceGame profileLaw =
      correlatedUtilityLaw program.pureFrontierGame profileLaw :=
  by
    simpa [pureFrontierTraceSurface] using
      bridge.implTraceGame_correlatedUtilityLaw_surface profileLaw

/-- Runtime refinements preserve the payoff-vector law induced by correlated
product mixed-pure frontier profile distributions. -/
theorem claim_runtime_refinement_preserves_mixed_pure_correlated_utility_law
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (mixedPureFrontierTraceSurface program) R)
    (profileLaw : PMF program.MixedPureFrontierProfile) :
    correlatedUtilityLaw bridge.implTraceGame profileLaw =
      correlatedUtilityLaw program.mixedPureFrontierGame profileLaw :=
  by
    simpa [mixedPureFrontierTraceSurface] using
      bridge.implTraceGame_correlatedUtilityLaw_surface profileLaw

/-- A behavioral runtime adequacy bridge induces a standard one-way Nash
deviation simulation from the behavioral frontier game to the implementation
trace game. -/
noncomputable def claim_runtime_refinement_behavioral_deviation_simulation
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R) :
    KernelGame.NashDeviationSimulation
      program.behavioralFrontierGame bridge.implTraceGame
      (GameTheory.Payoff P) :=
  by
    simpa [behavioralFrontierTraceSurface] using
      bridge.implTraceGame_nashDeviationSimulation

/-- A pure runtime adequacy bridge induces a standard one-way Nash deviation
simulation from the pure frontier game to the implementation trace game. -/
noncomputable def claim_runtime_refinement_pure_deviation_simulation
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R) :
    KernelGame.NashDeviationSimulation
      program.pureFrontierGame bridge.implTraceGame
      (GameTheory.Payoff P) :=
  by
    simpa [pureFrontierTraceSurface] using
      bridge.implTraceGame_nashDeviationSimulation

/-- A mixed-pure runtime adequacy bridge induces a standard one-way Nash
deviation simulation from the mixed-pure frontier game to the implementation
trace game. -/
noncomputable def claim_runtime_refinement_mixed_pure_deviation_simulation
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (mixedPureFrontierTraceSurface program) R) :
    KernelGame.NashDeviationSimulation
      program.mixedPureFrontierGame bridge.implTraceGame
      (GameTheory.Payoff P) :=
  by
    simpa [mixedPureFrontierTraceSurface] using
      bridge.implTraceGame_nashDeviationSimulation

/-- Under trace adequacy, behavioral correlated equilibrium is invariant
between the frontend surface and the implementation trace game. -/
theorem claim_runtime_refinement_behavioral_correlated_eq_iff
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R)
    (profileLaw : program.BehavioralFrontierCorrelatedProfile) :
    bridge.implTraceGame.IsCorrelatedEq profileLaw ↔
      program.BehavioralFrontierCorrelatedEq profileLaw :=
  by
    simpa [behavioralFrontierTraceSurface,
      WFProgram.BehavioralFrontierCorrelatedEq] using
      bridge.implTraceGame_correlatedEq_iff_surface_correlatedEq profileLaw

/-- Under trace adequacy, behavioral coarse-correlated equilibrium is invariant
between the frontend surface and the implementation trace game. -/
theorem claim_runtime_refinement_behavioral_coarse_correlated_eq_iff
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R)
    (profileLaw : program.BehavioralFrontierCorrelatedProfile) :
    bridge.implTraceGame.IsCoarseCorrelatedEq profileLaw ↔
      program.BehavioralFrontierCoarseCorrelatedEq profileLaw :=
  by
    simpa [behavioralFrontierTraceSurface,
      WFProgram.BehavioralFrontierCoarseCorrelatedEq] using
      bridge.implTraceGame_coarseCorrelatedEq_iff_surface_coarseCorrelatedEq
        profileLaw

/-- Under trace adequacy, pure correlated equilibrium is invariant between the
frontend surface and the implementation trace game. -/
theorem claim_runtime_refinement_pure_correlated_eq_iff
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R)
    (profileLaw : program.PureFrontierCorrelatedProfile) :
    bridge.implTraceGame.IsCorrelatedEq profileLaw ↔
      program.PureFrontierCorrelatedEq profileLaw :=
  by
    simpa [pureFrontierTraceSurface,
      WFProgram.PureFrontierCorrelatedEq] using
      bridge.implTraceGame_correlatedEq_iff_surface_correlatedEq profileLaw

/-- Under trace adequacy, pure coarse-correlated equilibrium is invariant
between the frontend surface and the implementation trace game. -/
theorem claim_runtime_refinement_pure_coarse_correlated_eq_iff
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R)
    (profileLaw : program.PureFrontierCorrelatedProfile) :
    bridge.implTraceGame.IsCoarseCorrelatedEq profileLaw ↔
      program.PureFrontierCoarseCorrelatedEq profileLaw :=
  by
    simpa [pureFrontierTraceSurface,
      WFProgram.PureFrontierCoarseCorrelatedEq] using
      bridge.implTraceGame_coarseCorrelatedEq_iff_surface_coarseCorrelatedEq
        profileLaw

/-- Under trace adequacy, behavioral Nash equilibrium is invariant between the
frontend surface and the implementation trace game. -/
theorem claim_runtime_refinement_behavioral_nash_iff
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R)
    (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.IsNash profile ↔
      program.BehavioralFrontierNash profile :=
  by
    simpa [behavioralFrontierTraceSurface,
      WFProgram.BehavioralFrontierNash] using
      bridge.implTraceGame_nash_iff_surface_nash profile

/-- Under trace adequacy, pure Nash equilibrium is invariant between the
frontend surface and the implementation trace game. -/
theorem claim_runtime_refinement_pure_nash_iff
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R)
    (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.IsNash profile ↔
      program.PureFrontierNash profile :=
  by
    simpa [pureFrontierTraceSurface,
      WFProgram.PureFrontierNash] using
      bridge.implTraceGame_nash_iff_surface_nash profile

/-- Under trace adequacy, product mixed-pure Nash equilibrium is invariant
between the frontend surface and the implementation trace game. -/
theorem claim_runtime_refinement_mixed_pure_nash_iff
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (mixedPureFrontierTraceSurface program) R)
    (profile : program.MixedPureFrontierProfile) :
    bridge.implTraceGame.IsNash profile ↔
      program.MixedPureFrontierNash profile :=
  by
    simpa [mixedPureFrontierTraceSurface,
      WFProgram.MixedPureFrontierNash] using
      bridge.implTraceGame_nash_iff_surface_nash profile

/-- Under trace adequacy, the implementation trace game has exactly the
behavioral frontier Nash equilibrium set. -/
theorem claim_runtime_refinement_behavioral_nash_set_eq
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R) :
    {profile : program.BehavioralFrontierProfile |
      bridge.implTraceGame.IsNash profile} =
    {profile : program.BehavioralFrontierProfile |
      program.BehavioralFrontierNash profile} :=
  by
    simpa [behavioralFrontierTraceSurface,
      WFProgram.BehavioralFrontierNash] using
      bridge.implTraceGame_nashSet_eq_surface_nashSet

/-- Under trace adequacy, the implementation trace game has exactly the pure
frontier Nash equilibrium set. -/
theorem claim_runtime_refinement_pure_nash_set_eq
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R) :
    {profile : program.PureFrontierProfile |
      bridge.implTraceGame.IsNash profile} =
    {profile : program.PureFrontierProfile |
      program.PureFrontierNash profile} :=
  by
    simpa [pureFrontierTraceSurface,
      WFProgram.PureFrontierNash] using
      bridge.implTraceGame_nashSet_eq_surface_nashSet

/-- Under trace adequacy, the implementation trace game has exactly the
mixed-pure frontier Nash equilibrium set. -/
theorem claim_runtime_refinement_mixed_pure_nash_set_eq
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (mixedPureFrontierTraceSurface program) R) :
    {profile : program.MixedPureFrontierProfile |
      bridge.implTraceGame.IsNash profile} =
    {profile : program.MixedPureFrontierProfile |
      program.MixedPureFrontierNash profile} :=
  by
    simpa [mixedPureFrontierTraceSurface,
      WFProgram.MixedPureFrontierNash] using
      bridge.implTraceGame_nashSet_eq_surface_nashSet

/-- Every trace-adequate behavioral implementation game of a finite-domain
checked program has a Nash equilibrium. -/
theorem claim_runtime_refinement_behavioral_nash_exists
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R) :
    ∃ profile : program.BehavioralFrontierProfile,
      bridge.implTraceGame.IsNash profile := by
  apply bridge.implTraceGame_nash_exists
  simpa [behavioralFrontierTraceSurface, BehavioralFrontierNash] using
    program.behavioralFrontier_nash_exists

/-- Every trace-adequate behavioral implementation game of a finite-domain
checked program has a correlated equilibrium. -/
theorem claim_runtime_refinement_behavioral_correlated_eq_exists
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R) :
    ∃ profileLaw : program.BehavioralFrontierCorrelatedProfile,
      bridge.implTraceGame.IsCorrelatedEq profileLaw := by
  apply bridge.implTraceGame_correlatedEq_exists
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierCorrelatedEq] using
    program.behavioralFrontier_correlatedEq_exists

/-- Every trace-adequate behavioral implementation game of a finite-domain
checked program has a coarse correlated equilibrium. -/
theorem claim_runtime_refinement_behavioral_coarse_correlated_eq_exists
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R) :
    ∃ profileLaw : program.BehavioralFrontierCorrelatedProfile,
      bridge.implTraceGame.IsCoarseCorrelatedEq profileLaw := by
  apply bridge.implTraceGame_coarseCorrelatedEq_exists
  simpa [behavioralFrontierTraceSurface,
    BehavioralFrontierCoarseCorrelatedEq] using
    program.behavioralFrontier_coarseCorrelatedEq_exists

/-- Behavioral frontier Nash profiles pull back to every trace-adequate
implementation game. -/
theorem claim_runtime_refinement_pulls_back_behavioral_nash
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R)
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile) :
    bridge.implTraceGame.IsNash profile :=
  by
    simpa [behavioralFrontierTraceSurface] using
      bridge.implTraceGame_nash_of_surface_nash hNash

/-- Pure frontier Nash profiles pull back to every trace-adequate
implementation game. -/
theorem claim_runtime_refinement_pulls_back_pure_nash
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R)
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile) :
    bridge.implTraceGame.IsNash profile :=
  by
    simpa [pureFrontierTraceSurface] using
      bridge.implTraceGame_nash_of_surface_nash hNash

/-- Product mixed-pure frontier Nash profiles pull back to every trace-adequate
implementation game. -/
theorem claim_runtime_refinement_pulls_back_mixed_pure_nash
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (mixedPureFrontierTraceSurface program) R)
    {profile : program.MixedPureFrontierProfile}
    (hNash : program.MixedPureFrontierNash profile) :
    bridge.implTraceGame.IsNash profile :=
  by
    simpa [mixedPureFrontierTraceSurface] using
      bridge.implTraceGame_nash_of_surface_nash hNash

end WFProgram

end Vegas
