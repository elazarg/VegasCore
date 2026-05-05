import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties
import Vegas.Finite
import Vegas.Protocol.Strategic

/-!
# Fixed-Program Pure Strategic Form

This file defines the pure strategic form for a fixed Vegas program. Its
strategy carrier is the reachable legal pure-strategy space of the finite
graph-machine FOSG at the program's syntax horizon.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Fixed-program pure strategic form of a Vegas program.

The outcome kernel is the checked graph-machine kernel at the bundle's context
proof. -/
noncomputable def pureKernelGame [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) :
    GameTheory.KernelGame P :=
  pureKernelGameAt g g.wctx LF

@[simp] theorem pureKernelGame_outcomeKernel
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : (pureKernelGame g LF).Profile) :
    (pureKernelGame g LF).outcomeKernel σ =
      (pureKernelGameAt g g.wctx LF).outcomeKernel σ := rfl

@[simp] theorem pureKernelGame_Strategy
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L) :
    (pureKernelGame g LF).Strategy = pureStrategyAt g g.wctx := rfl

/-- `pureKernelGame` is the machine-native pure kernel at `g.wctx`. -/
theorem pureKernelGame_eu
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : (pureKernelGame g LF).Profile) (who : P) :
    (pureKernelGame g LF).eu σ who =
      (pureKernelGameAt g g.wctx LF).eu σ who := rfl

/-- Pure Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureNash [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : (pureKernelGame g LF).Profile) : Prop :=
  (pureKernelGame g LF).IsNash σ

/-- Pure dominant strategy in the fixed-program Vegas strategic form. -/
def IsPureDominant [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (s : (pureKernelGame g LF).Strategy who) : Prop :=
  (pureKernelGame g LF).IsDominant who s

/-- Pure best response in the fixed-program Vegas strategic form. -/
def IsPureBestResponse [Fintype P] (g : WFProgram P L)
    (LF : FiniteValuation L) (who : P)
    (σ : (pureKernelGame g LF).Profile)
    (s : (pureKernelGame g LF).Strategy who) : Prop :=
  (pureKernelGame g LF).IsBestResponse who σ s

/-- Pure strict Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureStrictNash [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : (pureKernelGame g LF).Profile) : Prop :=
  (pureKernelGame g LF).IsStrictNash σ

/-- Exact potential for the fixed-program Vegas strategic form. -/
def IsPureExactPotential [Fintype P] (g : WFProgram P L)
    (LF : FiniteValuation L)
    (Φ : (pureKernelGame g LF).Profile → ℝ) : Prop :=
  (pureKernelGame g LF).IsExactPotential Φ

/-- Ordinal potential for the fixed-program Vegas strategic form. -/
def IsPureOrdinalPotential [Fintype P] (g : WFProgram P L)
    (LF : FiniteValuation L)
    (Φ : (pureKernelGame g LF).Profile → ℝ) : Prop :=
  (pureKernelGame g LF).IsOrdinalPotential Φ

end Vegas
