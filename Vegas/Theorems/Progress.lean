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
theorem protocolGraph_frontier_nonempty_of_not_terminal
    {G : ProtocolGraph P L} {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    cfg.frontier.Nonempty :=
  cfg.frontier_nonempty_of_not_terminal hterminal

/-- Checked source graphs have at least one legal concrete action for every
player-owned frontier node. -/
theorem checkedProgram_hasAvailablePlayerActions
    (g : WFProgram P L) :
    (syntaxProtocolGraph g).HasAvailablePlayerActions :=
  syntaxProtocolGraph_hasAvailablePlayerActions g

/-- Checked source graphs admit stable frontier rounds: executing one frontier
node preserves source-legal frontier actions for the remaining frontier. -/
theorem checkedProgram_hasStableFrontierRounds
    (g : WFProgram P L) :
    (syntaxProtocolGraph g).HasStableFrontierRounds :=
  syntaxProtocolGraph_hasStableFrontierRounds g

/-- The bounded syntax-graph FOSG view has the legal-observability property
needed by Kuhn realization. -/
theorem checkedProgram_boundedFOSG_legalObservable
    (g : WFProgram P L) (horizon : Nat) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).LegalObservable :=
  syntaxGraphFOSGView_toBoundedFOSG_legalObservable g horizon

/-- Source-linear reading has a ready next event whenever the syntax graph is
nonterminal. -/
theorem checkedProgram_linearRead_sufficient
    (g : WFProgram P L)
    (cfg : (syntaxProtocolGraph g).Configuration)
    (hterminal : ¬ cfg.terminal) :
    ∃ node : ProgramNode g.prog,
      node ∈ cfg.frontier ∧
        ∀ other : ProgramNode g.prog,
          other ∈ ProgramNode.finset g.prog →
            (cfg.result other).isNone →
              node.rank ≤ other.rank :=
  syntaxLinearRead_sufficient g cfg hterminal

/-- Omniscient progress for the bounded syntax-graph FOSG: every nonterminal
state admits at least one legal joint action. -/
theorem checkedProgram_boundedFOSG_exists_legal_of_not_terminal
    (g : WFProgram P L) (horizon : Nat)
    {state : (syntaxGraphMachine g).BoundedState horizon}
    (hterminal :
      ¬ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal state) :
    ∃ action : JointAction (syntaxGraphFOSGView g).Act,
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).legal state action :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).exists_legal_of_not_terminal
    hterminal

/-- The bounded syntax-graph FOSG reaches terminal/cutoff by its presentation
horizon. -/
theorem checkedProgram_boundedFOSG_boundedHorizon
    (g : WFProgram P L) (horizon : Nat) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).BoundedHorizon horizon :=
  (syntaxGraphFOSGView g).toBoundedFOSG_boundedHorizon horizon

/-- Terminal bounded syntax-graph FOSG states have no legal joint action. -/
theorem checkedProgram_boundedFOSG_not_legal_of_terminal
    (g : WFProgram P L) (horizon : Nat)
    {state : (syntaxGraphMachine g).BoundedState horizon}
    {action : JointAction (syntaxGraphFOSGView g).Act}
    (hterminal :
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal state) :
    ¬ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).legal state action :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).not_legal_of_terminal
    hterminal

/-- Joint-action legality in the bounded syntax-graph FOSG decomposes into
nonterminality and per-player local optional-move legality. -/
theorem checkedProgram_boundedFOSG_legal_iff_forall_locallyLegal
    (g : WFProgram P L) (horizon : Nat)
    {state : (syntaxGraphMachine g).BoundedState horizon}
    {action : JointAction (syntaxGraphFOSGView g).Act} :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).legal state action ↔
      ¬ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal state ∧
        ∀ who,
          ((syntaxGraphFOSGView g).toBoundedFOSG horizon).locallyLegalAtState
            state who (action who) :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).legal_iff_forall

end Vegas
