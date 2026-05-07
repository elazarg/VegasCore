import Vegas.Protocol.LinearRead

/-!
# Progress Theorems

Project-facing names for graph and bounded-FOSG progress facts: checked
programs have executable next steps until terminal/cutoff states are reached.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A nonterminal protocol-graph configuration has a nonempty executable
frontier. This is the graph-level progress theorem. -/
theorem eventGraph_frontier_nonempty_of_not_terminal
    {G : EventGraph P L} {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    cfg.frontier.Nonempty :=
  cfg.frontier_nonempty_of_not_terminal hterminal

/-- Checked program event graphs have at least one legal concrete action for every
player-owned frontier node. -/
theorem checkedProgram_hasAvailablePlayerActions
    (g : WFProgram P L) :
    (programEventGraph g).HasAvailablePlayerActions :=
  programEventGraph_hasAvailablePlayerActions g

/-- Checked program event graphs admit stable frontier rounds: executing one frontier
node preserves source-legal frontier actions for the remaining frontier. -/
theorem checkedProgram_hasStableFrontierRounds
    (g : WFProgram P L) :
    (programEventGraph g).HasStableFrontierRounds :=
  programEventGraph_hasStableFrontierRounds g

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
