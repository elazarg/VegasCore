import Vegas.Examples.Prisoners
import Vegas.Examples.MatchingPennies
import Vegas.Examples.BattleOfTheSexes
import Vegas.Examples.MontyHall
import Vegas.Examples.SyntaxConstructors
import Vegas.Protocol.EFG

/-!
# EFG translation examples

These examples instantiate the canonical FOSG-to-augmented-EFG bridge on
checked Vegas programs. The expected EFG is the bridge presentation: each
bounded FOSG round is serialized into EFG decision nodes, and terminal EFG
outcomes are native bounded FOSG histories.
-/

namespace Vegas
namespace Examples
namespace EFGTranslation

open GameTheory

namespace Prisoners

noncomputable def efg : EFG.EFGGame :=
  syntaxGraphEFGAt Examples.Prisoners.game

theorem player_count :
    efg.inf.n = Fintype.card Examples.Prisoners.Player := rfl

theorem outcomeKernel_map_publicOutcome
    (β : (pmfBehavioralKernelGame Examples.Prisoners.game).Profile) :
    PMF.map (syntaxGraphEFGPublicOutcomeAt Examples.Prisoners.game)
        (efg.toKernelGame.outcomeKernel
          (syntaxGraphEFGBehavioralProfileAt Examples.Prisoners.game β)) =
      (pmfBehavioralKernelGame Examples.Prisoners.game).outcomeKernel β :=
  syntaxGraphEFGAt_outcomeKernel_map_publicOutcome
    Examples.Prisoners.game β

/-- The generated Prisoner's Dilemma EFG starts with a decision node. -/
theorem tree_root_decision :
    ∃ (p0 : efg.inf.Player) (I0 : efg.inf.Infoset p0)
      (next0 : efg.inf.Act I0 → EFG.GameTree efg.inf efg.Outcome),
      efg.tree = EFG.GameTree.decision I0 next0 := by
  unfold efg syntaxGraphEFGAt
  change ∃ (p0 : _) (I0 : _) (next0 : _),
    GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := syntaxGraphBoundedFOSGAt Examples.Prisoners.game)
        (syntaxSteps Examples.Prisoners.game.prog) (3 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (syntaxGraphBoundedFOSGAt Examples.Prisoners.game)) =
      EFG.GameTree.decision I0 next0
  rw [GameTheory.FOSG.AugmentedEFGBridge.tree_fromHistory_succ_nonterminal]
  · rw [GameTheory.FOSG.AugmentedEFGBridge.Tree.choosePlayersFrom]
    have hcard : 0 < Fintype.card Examples.Prisoners.Player := by decide
    simp [hcard]
  · exact syntaxGraphBoundedFOSGAt_root_not_terminal_of_node
      Examples.Prisoners.game
      (ProgramNode.commitHere : ProgramNode Examples.Prisoners.game.prog)
      (by decide)

/-- More precise first-round shape: the canonical EFG serializes the first
Prisoner's Dilemma FOSG round as two player decisions and then a chance
transition. -/
theorem tree_first_round_two_decisions_then_chance :
    EFG.GameTree.HasDecisionChainThenChance
      (Fintype.card Examples.Prisoners.Player) efg.tree := by
  unfold efg syntaxGraphEFGAt
  change EFG.GameTree.HasDecisionChainThenChance
    (Fintype.card Examples.Prisoners.Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := syntaxGraphBoundedFOSGAt Examples.Prisoners.game)
        (syntaxSteps Examples.Prisoners.game.prog) (3 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (syntaxGraphBoundedFOSGAt Examples.Prisoners.game)))
  rw [GameTheory.FOSG.AugmentedEFGBridge.tree_fromHistory_succ_nonterminal]
  · simp [GameTheory.FOSG.AugmentedEFGBridge.Tree.choosePlayersFrom,
      show Fintype.card Examples.Prisoners.Player = 2 by decide]
  · exact syntaxGraphBoundedFOSGAt_root_not_terminal_of_node
      Examples.Prisoners.game
      (ProgramNode.commitHere : ProgramNode Examples.Prisoners.game.prog)
      (by decide)

end Prisoners

namespace MatchingPennies

noncomputable def efg : EFG.EFGGame :=
  syntaxGraphEFGAt Examples.MatchingPennies.game

theorem player_count :
    efg.inf.n = Fintype.card Examples.MatchingPennies.Player := rfl

theorem outcomeKernel_map_publicOutcome
    (β : (pmfBehavioralKernelGame Examples.MatchingPennies.game).Profile) :
    PMF.map (syntaxGraphEFGPublicOutcomeAt Examples.MatchingPennies.game)
        (efg.toKernelGame.outcomeKernel
          (syntaxGraphEFGBehavioralProfileAt Examples.MatchingPennies.game β)) =
      (pmfBehavioralKernelGame Examples.MatchingPennies.game).outcomeKernel β :=
  syntaxGraphEFGAt_outcomeKernel_map_publicOutcome
    Examples.MatchingPennies.game β

/-- The generated Matching Pennies EFG starts with a decision node. -/
theorem tree_root_decision :
    ∃ (p0 : efg.inf.Player) (I0 : efg.inf.Infoset p0)
      (next0 : efg.inf.Act I0 → EFG.GameTree efg.inf efg.Outcome),
      efg.tree = EFG.GameTree.decision I0 next0 := by
  unfold efg syntaxGraphEFGAt
  change ∃ (p0 : _) (I0 : _) (next0 : _),
    GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := syntaxGraphBoundedFOSGAt Examples.MatchingPennies.game)
        (syntaxSteps Examples.MatchingPennies.game.prog) (3 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (syntaxGraphBoundedFOSGAt Examples.MatchingPennies.game)) =
      EFG.GameTree.decision I0 next0
  rw [GameTheory.FOSG.AugmentedEFGBridge.tree_fromHistory_succ_nonterminal]
  · rw [GameTheory.FOSG.AugmentedEFGBridge.Tree.choosePlayersFrom]
    have hcard : 0 < Fintype.card Examples.MatchingPennies.Player := by decide
    simp [hcard]
  · exact syntaxGraphBoundedFOSGAt_root_not_terminal_of_node
      Examples.MatchingPennies.game
      (ProgramNode.commitHere : ProgramNode Examples.MatchingPennies.game.prog)
      (by decide)

/-- Matching Pennies first-round tree spine: two decisions, then chance. -/
theorem tree_first_round_two_decisions_then_chance :
    EFG.GameTree.HasDecisionChainThenChance
      (Fintype.card Examples.MatchingPennies.Player) efg.tree := by
  unfold efg syntaxGraphEFGAt
  change EFG.GameTree.HasDecisionChainThenChance
    (Fintype.card Examples.MatchingPennies.Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := syntaxGraphBoundedFOSGAt Examples.MatchingPennies.game)
        (syntaxSteps Examples.MatchingPennies.game.prog) (3 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (syntaxGraphBoundedFOSGAt Examples.MatchingPennies.game)))
  rw [GameTheory.FOSG.AugmentedEFGBridge.tree_fromHistory_succ_nonterminal]
  · simp [GameTheory.FOSG.AugmentedEFGBridge.Tree.choosePlayersFrom,
      show Fintype.card Examples.MatchingPennies.Player = 2 by decide]
  · exact syntaxGraphBoundedFOSGAt_root_not_terminal_of_node
      Examples.MatchingPennies.game
      (ProgramNode.commitHere : ProgramNode Examples.MatchingPennies.game.prog)
      (by decide)

end MatchingPennies

namespace BattleOfTheSexes

noncomputable def efg : EFG.EFGGame :=
  syntaxGraphEFGAt Examples.BattleOfTheSexes.game

theorem player_count :
    efg.inf.n = Fintype.card Examples.BattleOfTheSexes.Player := rfl

theorem outcomeKernel_map_publicOutcome
    (β : (pmfBehavioralKernelGame Examples.BattleOfTheSexes.game).Profile) :
    PMF.map (syntaxGraphEFGPublicOutcomeAt Examples.BattleOfTheSexes.game)
        (efg.toKernelGame.outcomeKernel
          (syntaxGraphEFGBehavioralProfileAt Examples.BattleOfTheSexes.game β)) =
      (pmfBehavioralKernelGame Examples.BattleOfTheSexes.game).outcomeKernel β :=
  syntaxGraphEFGAt_outcomeKernel_map_publicOutcome
    Examples.BattleOfTheSexes.game β

/-- Battle of the Sexes first-round tree spine: two decisions, then chance. -/
theorem tree_first_round_two_decisions_then_chance :
    EFG.GameTree.HasDecisionChainThenChance
      (Fintype.card Examples.BattleOfTheSexes.Player) efg.tree := by
  unfold efg syntaxGraphEFGAt
  change EFG.GameTree.HasDecisionChainThenChance
    (Fintype.card Examples.BattleOfTheSexes.Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := syntaxGraphBoundedFOSGAt Examples.BattleOfTheSexes.game)
        (syntaxSteps Examples.BattleOfTheSexes.game.prog) (3 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (syntaxGraphBoundedFOSGAt Examples.BattleOfTheSexes.game)))
  rw [GameTheory.FOSG.AugmentedEFGBridge.tree_fromHistory_succ_nonterminal]
  · simp [GameTheory.FOSG.AugmentedEFGBridge.Tree.choosePlayersFrom,
      show Fintype.card Examples.BattleOfTheSexes.Player = 2 by decide]
  · exact syntaxGraphBoundedFOSGAt_root_not_terminal_of_node
      Examples.BattleOfTheSexes.game
      (ProgramNode.commitHere : ProgramNode Examples.BattleOfTheSexes.game.prog)
      (by decide)

end BattleOfTheSexes

namespace MontyHall

noncomputable def efg : EFG.EFGGame :=
  syntaxGraphEFGAt Examples.MontyHall.game

theorem player_count :
    efg.inf.n = Fintype.card Examples.MontyHall.Player := rfl

theorem outcomeKernel_map_publicOutcome
    (β : (pmfBehavioralKernelGame Examples.MontyHall.game).Profile) :
    PMF.map (syntaxGraphEFGPublicOutcomeAt Examples.MontyHall.game)
        (efg.toKernelGame.outcomeKernel
          (syntaxGraphEFGBehavioralProfileAt Examples.MontyHall.game β)) =
      (pmfBehavioralKernelGame Examples.MontyHall.game).outcomeKernel β :=
  syntaxGraphEFGAt_outcomeKernel_map_publicOutcome
    Examples.MontyHall.game β

/-- Monty Hall first-round tree spine: two decisions, then chance. The first
round includes the bridge's serial decision opportunities for both players,
even though only the currently active player's translated strategy has
non-`none` support. -/
theorem tree_first_round_two_decisions_then_chance :
    EFG.GameTree.HasDecisionChainThenChance
      (Fintype.card Examples.MontyHall.Player) efg.tree := by
  unfold efg syntaxGraphEFGAt
  change EFG.GameTree.HasDecisionChainThenChance
    (Fintype.card Examples.MontyHall.Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := syntaxGraphBoundedFOSGAt Examples.MontyHall.game)
        (syntaxSteps Examples.MontyHall.game.prog) (7 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (syntaxGraphBoundedFOSGAt Examples.MontyHall.game)))
  rw [GameTheory.FOSG.AugmentedEFGBridge.tree_fromHistory_succ_nonterminal]
  · simp [GameTheory.FOSG.AugmentedEFGBridge.Tree.choosePlayersFrom,
      show Fintype.card Examples.MontyHall.Player = 2 by decide]
  · exact syntaxGraphBoundedFOSGAt_root_not_terminal_of_node
      Examples.MontyHall.game
      (ProgramNode.commitHere : ProgramNode Examples.MontyHall.game.prog)
      (by decide)

end MontyHall

namespace SyntaxConstructors

noncomputable def efg : EFG.EFGGame :=
  syntaxGraphEFGAt Examples.SyntaxConstructors.game

theorem player_count :
    efg.inf.n = Fintype.card Examples.SyntaxConstructors.Player := rfl

theorem outcomeKernel_map_publicOutcome
    (β : (pmfBehavioralKernelGame Examples.SyntaxConstructors.game).Profile) :
    PMF.map (syntaxGraphEFGPublicOutcomeAt Examples.SyntaxConstructors.game)
        (efg.toKernelGame.outcomeKernel
          (syntaxGraphEFGBehavioralProfileAt Examples.SyntaxConstructors.game β)) =
      (pmfBehavioralKernelGame Examples.SyntaxConstructors.game).outcomeKernel β :=
  syntaxGraphEFGAt_outcomeKernel_map_publicOutcome
    Examples.SyntaxConstructors.game β

/-- The constructor-smoke example has one player, so each nonterminal bridge
round is one decision opportunity followed by chance. The first source event is
internal; the decision opportunity is the bridge's uniform optional-move layer. -/
theorem tree_first_round_one_decision_then_chance :
    EFG.GameTree.HasDecisionChainThenChance
      (Fintype.card Examples.SyntaxConstructors.Player) efg.tree := by
  unfold efg syntaxGraphEFGAt
  change EFG.GameTree.HasDecisionChainThenChance
    (Fintype.card Examples.SyntaxConstructors.Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := syntaxGraphBoundedFOSGAt Examples.SyntaxConstructors.game)
        (syntaxSteps Examples.SyntaxConstructors.game.prog) (1 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (syntaxGraphBoundedFOSGAt Examples.SyntaxConstructors.game)))
  rw [GameTheory.FOSG.AugmentedEFGBridge.tree_fromHistory_succ_nonterminal]
  · simp [GameTheory.FOSG.AugmentedEFGBridge.Tree.choosePlayersFrom,
      show Fintype.card Examples.SyntaxConstructors.Player = 1 by decide]
  · exact syntaxGraphBoundedFOSGAt_root_not_terminal_of_node
      Examples.SyntaxConstructors.game
      (ProgramNode.letHere : ProgramNode Examples.SyntaxConstructors.game.prog)
      (by decide)

end SyntaxConstructors

end EFGTranslation
end Examples
end Vegas
