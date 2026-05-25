import Vegas.Core.ToEventGraph.Games

/-!
# Kernel-game export tables

This module provides an in-Lean finite strategy table for solver or serializer
adapters.  It does not prescribe an external file format; it packages the
finite players, finite strategies, outcome kernel, and utility function without
reinterpretation.
-/

namespace Vegas

namespace Export

open GameTheory

/-- Finite strategy-table view of a kernel game.

The outcome type is not required to be finite.  Compiled Vegas outcome carriers
can live in an ambient infinite type even when every generated distribution has
finite support. -/
structure KernelGameExport (P : Type) where
  Strategy : P → Type
  Outcome : Type
  players : List P
  strategies : (player : P) → List (Strategy player)
  outcomeProb : ((player : P) → Strategy player) → Outcome → ENNReal
  utility : Outcome → P → ℝ

namespace KernelGameExport

variable {P : Type}

/-- Export any kernel game with finite player and strategy carriers. -/
noncomputable def ofKernelGame
    [Fintype P] (game : KernelGame P)
    [∀ player, Fintype (game.Strategy player)] :
    KernelGameExport P where
  Strategy := game.Strategy
  Outcome := game.Outcome
  players := Fintype.elems.toList
  strategies := fun player =>
    (Fintype.elems (α := game.Strategy player)).toList
  outcomeProb := fun profile outcome =>
    game.outcomeKernel profile outcome
  utility := game.utility

@[simp] theorem ofKernelGame_outcomeProb
    [Fintype P] (game : KernelGame P)
    [∀ player, Fintype (game.Strategy player)]
    (profile : game.Profile) (outcome : game.Outcome) :
    (ofKernelGame game).outcomeProb profile outcome =
      game.outcomeKernel profile outcome := rfl

@[simp] theorem ofKernelGame_utility
    [Fintype P] (game : KernelGame P)
    [∀ player, Fintype (game.Strategy player)]
    (outcome : game.Outcome) (player : P) :
    (ofKernelGame game).utility outcome player =
      game.utility outcome player := rfl

end KernelGameExport

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Export table for a checked program's pure-strategy frontier game. -/
noncomputable def pureFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGameExport P := by
  classical
  letI :
      ∀ player, Fintype (program.pureFrontierGame.Strategy player) :=
    fun player => program.frontierSemantics.pureStrategyFintype player
  exact KernelGameExport.ofKernelGame program.pureFrontierGame

/-- Export table for the pure-strategy terminal-public frontier game. -/
noncomputable def pureTerminalPublicFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGameExport P := by
  classical
  letI :
      ∀ player,
        Fintype (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      change Fintype (program.pureFrontierGame.Strategy player)
      exact program.frontierSemantics.pureStrategyFintype player
  exact KernelGameExport.ofKernelGame
    program.pureTerminalPublicFrontierGame

/-- Export table for the pure-strategy frontier game with full round histories
as outcomes. -/
noncomputable def pureFrontierHistoryGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGameExport P := by
  classical
  letI :
      ∀ player,
        Fintype (program.pureFrontierHistoryKernelGame.Strategy player) :=
    fun player => by
      change Fintype (program.pureFrontierGame.Strategy player)
      exact program.frontierSemantics.pureStrategyFintype player
  exact KernelGameExport.ofKernelGame
    program.pureFrontierHistoryKernelGame

end Export

end Vegas
