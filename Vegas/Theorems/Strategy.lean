import Vegas.Frontier.Games
import Vegas.Frontier.SolutionConcepts
import GameTheory.Concepts.Dominance.DominanceNash

/-!
# Strategy facts

The native strategic surface is the completed frontier game.  Strategies are
functions of the player's frontier information state, and the solution-concept
module supplies the program-facing game-theory vocabulary for those games.
-/

namespace Vegas

open GameTheory

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- In the checked program's pure frontier semantics, when a realized step
contains a move by `player`, that move is recorded in that player's information
state before the step observation. -/
theorem pureFrontierStep_recordsOwnAction
    (program : WFProgram P L) [FiniteDomains program]
    {player : P}
    (step :
      (program.frontierSemantics.pure.view).BoundedStep
        program.frontierSemantics.horizon)
    {action : (program.frontierSemantics.pure.view).Act player}
    (hact : step.ownAction? player = some action) :
    step.playerView player =
      [.act action, .obs (step.privateObs player) step.publicObs] :=
  Machine.RoundView.BoundedStep.playerView_of_ownAction?_eq_some
    step player hact

/-- In the checked program's behavioral frontier semantics, when a realized
step contains a move by `player`, that move is recorded in that player's
information state before the step observation. -/
theorem behavioralFrontierStep_recordsOwnAction
    (program : WFProgram P L) [FiniteDomains program]
    {player : P}
    (step :
      (program.frontierSemantics.behavioral.view).BoundedStep
        program.frontierSemantics.horizon)
    {action : (program.frontierSemantics.behavioral.view).Act player}
    (hact : step.ownAction? player = some action) :
    step.playerView player =
      [.act action, .obs (step.privateObs player) step.publicObs] :=
  Machine.RoundView.BoundedStep.playerView_of_ownAction?_eq_some
    step player hact

/-- Pure frontier strategies depend only on the player's information state. -/
theorem pureFrontierStrategy_respectsView
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.PureFrontierStrategy player)
    {left right : program.PureFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player left) =
      strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player right) :=
  program.pureFrontierStrategy_eq_of_playerView_eq strategy hview

/-- Behavioral frontier strategies depend only on the player's information
state. -/
theorem behavioralFrontierStrategy_respectsView
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

/-! ## Menus and legality are information-state facts -/

/-- In the pure frontier game, equal player information states have exactly the
same legal optional moves. -/
theorem pureFrontier_availableMoves_eq_of_playerView_eq
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} {left right : program.PureFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    (program.frontierSemantics.pure.view).boundedAvailableMoves
        program.frontierSemantics.horizon left player =
      (program.frontierSemantics.pure.view).boundedAvailableMoves
        program.frontierSemantics.horizon right player :=
  program.frontierSemantics.menus player left right hview

/-- In the behavioral frontier game, equal player information states have
exactly the same legal optional moves. -/
theorem behavioralFrontier_availableMoves_eq_of_playerView_eq
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} {left right : program.BehavioralFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    (program.frontierSemantics.behavioral.view).boundedAvailableMoves
        program.frontierSemantics.horizon left player =
      (program.frontierSemantics.behavioral.view).boundedAvailableMoves
        program.frontierSemantics.horizon right player :=
  program.frontierSemantics.menus player left right hview

/-- Pure frontier strategies select only legal moves at reachable completed
frontier histories. -/
theorem pureFrontierStrategy_selectsLegalMove
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.PureFrontierStrategy player)
    (history : program.PureFrontierHistory) :
    strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player history) ∈
      (program.frontierSemantics.pure.view).boundedAvailableMoves
          program.frontierSemantics.horizon history player :=
  program.pureFrontierStrategy_chooses_available strategy history

/-- Behavioral frontier strategies put positive probability only on legal
moves at reachable completed frontier histories. -/
theorem behavioralFrontierStrategy_supportsOnlyLegalMoves
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.BehavioralFrontierStrategy player)
    (history : program.BehavioralFrontierHistory)
    {move : Option ((program.frontierSemantics.behavioral.view).Act player)}
    (hmove :
      move ∈
        (strategy.1
          ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
              program.frontierSemantics.horizon player history)).support) :
    move ∈
      (program.frontierSemantics.behavioral.view).boundedAvailableMoves
          program.frontierSemantics.horizon history player :=
  program.behavioralFrontierStrategy_supports_available
    strategy history hmove

/-! ## Dominance and equilibrium strategy facts -/

/-- A pure frontier Nash profile cannot use a strategy strictly dominated by
another strategy. -/
theorem pureFrontier_nash_not_strictly_dominated_strategy
    (program : WFProgram P L) [FiniteDomains program]
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile)
    {player : P} {dominating : program.PureFrontierStrategy player}
    (hdom :
      program.PureFrontierStrictlyDominates player dominating
        (profile player)) :
    False :=
  hdom.not_nash hNash

/-- A behavioral frontier Nash profile cannot use a strategy strictly
dominated by another strategy. -/
theorem behavioralFrontier_nash_not_strictly_dominated_strategy
    (program : WFProgram P L) [FiniteDomains program]
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile)
    {player : P} {dominating : program.BehavioralFrontierStrategy player}
    (hdom :
      program.BehavioralFrontierStrictlyDominates player dominating
        (profile player)) :
    False :=
  hdom.not_nash hNash

end WFProgram

end Vegas
