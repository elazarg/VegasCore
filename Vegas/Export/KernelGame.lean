import Vegas.Strategic.BehavioralPMF

/-!
# Finite kernel-game export

This module provides a small in-Lean export object for solver adapters.  It is
not a file format; it is the checked finite table that a JSON/CSV/solver
backend can serialize without reinterpreting Vegas semantics.
-/

namespace Vegas

namespace Export

open GameTheory

/-- Finite strategy-table view of a kernel game.

The table keeps the original strategy and outcome types, exposes finite
player/strategy enumerations, and exposes the kernel/utility functions a
downstream serializer needs.  The outcome type is not required to be finite:
Vegas payoff outcomes use integer-valued finite maps, so their ambient type is
infinite even when each generated distribution has finite support. -/
structure KernelGameExport (P : Type) where
  Strategy : P → Type
  Outcome : Type
  players : List P
  strategies : ∀ player, List (Strategy player)
  outcomeProb : (∀ player, Strategy player) → Outcome → ENNReal
  utility : Outcome → P → ℝ

namespace KernelGameExport

variable {P : Type}

/-- Export any kernel game with finite player and strategy sets as an explicit
strategy table plus kernel/utility oracles. -/
noncomputable def ofKernelGame
    [Fintype P] (G : KernelGame P)
    [∀ player, Fintype (G.Strategy player)] :
    KernelGameExport P where
  Strategy := G.Strategy
  Outcome := G.Outcome
  players := Fintype.elems.toList
  strategies := fun player => (Fintype.elems (α := G.Strategy player)).toList
  outcomeProb := fun σ outcome => G.outcomeKernel σ outcome
  utility := G.utility

@[simp] theorem ofKernelGame_outcomeProb
    [Fintype P] (G : KernelGame P)
    [∀ player, Fintype (G.Strategy player)]
    (σ : G.Profile) (outcome : G.Outcome) :
    (ofKernelGame G).outcomeProb σ outcome = G.outcomeKernel σ outcome := rfl

@[simp] theorem ofKernelGame_utility
    [Fintype P] (G : KernelGame P)
    [∀ player, Fintype (G.Strategy player)]
    (outcome : G.Outcome) (player : P) :
    (ofKernelGame G).utility outcome player = G.utility outcome player := rfl

end KernelGameExport

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Finite strategy export table for the pure payoff-vector Vegas game. -/
noncomputable def pureKernelGameExport
    (g : WFProgram P L) [FiniteDomains g] :
    KernelGameExport P :=
  KernelGameExport.ofKernelGame (pureKernelGameAt g)

/-- Finite strategy export table for the pure blocked-trace Vegas game. -/
noncomputable def pureBlockedTraceKernelGameExport
    (g : WFProgram P L) [FiniteDomains g] :
    KernelGameExport P := by
  classical
  letI : ∀ player, Fintype ((pureBlockedTraceKernelGameAt g).Strategy player) := by
    intro player
    change Fintype (pureStrategyAt g player)
    infer_instance
  exact KernelGameExport.ofKernelGame (pureBlockedTraceKernelGameAt g)

end Export

end Vegas
