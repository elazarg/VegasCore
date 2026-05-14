import Vegas.Core.LinearRead
import Vegas.GameBridge.FOSG.FromCore

/-!
# Checked-Program Progress

Progress and bounded-FOSG availability facts for checked `VegasCore` programs.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Every declared read of a generated frontier node has a value. -/
theorem checkedProgram_readsAvailableAtFrontier
    (g : WFProgram P L) :
    programReadsAvailableAtFrontier g :=
  programReadsAvailableAtFrontier_of_wfProgram g

/-- Pointwise form of read availability at generated frontiers. -/
theorem checkedProgram_frontier_read_value_isSome
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    (hfrontier : node ∈ cfg.frontier)
    {read : ProgramField g.prog}
    (hread : read ∈ (ProgramNode.sem g.obligations node).reads) :
    (ProgramField.value? g.env cfg.result read).isSome :=
  programReadsAvailableAtFrontier_of_wfProgram
    g cfg hfrontier read hread

/-- Checked program event graphs have at least one legal concrete action for every
player-owned frontier node. -/
theorem checkedProgram_hasAvailablePlayerActions
    (g : WFProgram P L) :
    (programEventGraph g).HasAvailablePlayerActions :=
  programEventGraph_hasAvailablePlayerActions g

/-- The bounded event-graph FOSG view has the legal-observability property
needed by Kuhn realization. -/
theorem checkedProgram_boundedFOSG_legalObservable
    (g : WFProgram P L) (horizon : Nat) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).LegalObservable :=
  eventGraphFOSGView_toBoundedFOSG_legalObservable g horizon

/-- Source-linear reading has an enabled next event whenever the event graph is
nonterminal. -/
theorem checkedProgram_linearRead_sufficient
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration)
    (hterminal : ¬ cfg.terminal) :
    ∃ node : ProgramNode g.prog,
      node ∈ cfg.frontier ∧
        ∀ other : ProgramNode g.prog,
          other ∈ ProgramNode.finset g.prog →
            (cfg.result other).isNone →
              node.rank ≤ other.rank :=
  syntaxLinearRead_sufficient g cfg hterminal

/-- Omniscient progress for the bounded event-graph FOSG: every nonterminal
state admits at least one legal joint action. -/
theorem checkedProgram_boundedFOSG_exists_legal_of_not_terminal
    (g : WFProgram P L) (horizon : Nat)
    {state : (eventGraphMachine g).BoundedState horizon}
    (hterminal :
      ¬ ((eventGraphFOSGView g).toBoundedFOSG horizon).terminal state) :
    ∃ action : JointAction (eventGraphFOSGView g).Act,
      ((eventGraphFOSGView g).toBoundedFOSG horizon).legal state action :=
  ((eventGraphFOSGView g).toBoundedFOSG horizon).exists_legal_of_not_terminal
    hterminal

/-- The bounded event-graph FOSG reaches terminal/cutoff by its presentation
horizon. -/
theorem checkedProgram_boundedFOSG_boundedHorizon
    (g : WFProgram P L) (horizon : Nat) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).BoundedHorizon horizon :=
  (eventGraphFOSGView g).toBoundedFOSG_boundedHorizon horizon

/-- Terminal bounded event-graph FOSG states have no legal joint action. -/
theorem checkedProgram_boundedFOSG_not_legal_of_terminal
    (g : WFProgram P L) (horizon : Nat)
    {state : (eventGraphMachine g).BoundedState horizon}
    {action : JointAction (eventGraphFOSGView g).Act}
    (hterminal :
      ((eventGraphFOSGView g).toBoundedFOSG horizon).terminal state) :
    ¬ ((eventGraphFOSGView g).toBoundedFOSG horizon).legal state action :=
  ((eventGraphFOSGView g).toBoundedFOSG horizon).not_legal_of_terminal
    hterminal

/-- Joint-action legality in the bounded event-graph FOSG decomposes into
nonterminality and per-player local optional-move legality. -/
theorem checkedProgram_boundedFOSG_legal_iff_forall_locallyLegal
    (g : WFProgram P L) (horizon : Nat)
    {state : (eventGraphMachine g).BoundedState horizon}
    {action : JointAction (eventGraphFOSGView g).Act} :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).legal state action ↔
      ¬ ((eventGraphFOSGView g).toBoundedFOSG horizon).terminal state ∧
        ∀ who,
          ((eventGraphFOSGView g).toBoundedFOSG horizon).locallyLegalAtState
            state who (action who) :=
  ((eventGraphFOSGView g).toBoundedFOSG horizon).legal_iff_forall

/-- Checked event graphs cannot deadlock before terminality. -/
theorem checkedProgram_no_deadlock_before_terminal
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    (hterminal : ¬ cfg.terminal) :
    cfg.frontier.Nonempty :=
  cfg.frontier_nonempty_of_not_terminal hterminal

/-- In every nonterminal checked event-graph configuration, a rank-minimal
unfinished source node is executable. -/
theorem checkedProgram_every_source_node_eventually_frontier_or_done
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    (hterminal : ¬ cfg.terminal) :
    ∃ node : ProgramNode g.prog,
      node ∈ cfg.frontier ∧
        ∀ other : ProgramNode g.prog,
          other ∈ ProgramNode.finset g.prog →
            (cfg.result other).isNone →
              node.rank ≤ other.rank :=
  syntaxLinearRead_sufficient g cfg hterminal

/-- Event-graph terminality is exactly completion of all event nodes. -/
theorem checkedProgram_terminal_iff_all_nodes_done
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration) :
    cfg.terminal ↔
      (programEventGraph g).nodes ⊆
        (programEventGraph g).done cfg.result :=
  Iff.rfl

end Vegas
