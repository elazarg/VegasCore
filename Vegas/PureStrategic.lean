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
    (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  pureKernelGameAt g g.wctx

@[simp] theorem pureKernelGame_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pureKernelGame g).Profile) :
    (pureKernelGame g).outcomeKernel σ =
      (pureKernelGameAt g g.wctx).outcomeKernel σ := rfl

@[simp] theorem pureKernelGame_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGame g).Strategy = pureStrategyAt g g.wctx := rfl

/-- `pureKernelGame` is the machine-native pure kernel at `g.wctx`. -/
theorem pureKernelGame_eu
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pureKernelGame g).Profile) (who : P) :
    (pureKernelGame g).eu σ who =
      (pureKernelGameAt g g.wctx).eu σ who := rfl

/-- Pure Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureNash [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pureKernelGame g).Profile) : Prop :=
  (pureKernelGame g).IsNash σ

/-- Pure dominant strategy in the fixed-program Vegas strategic form. -/
def IsPureDominant [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s : (pureKernelGame g).Strategy who) : Prop :=
  (pureKernelGame g).IsDominant who s

/-- Pure best response in the fixed-program Vegas strategic form. -/
def IsPureBestResponse [Fintype P] (g : WFProgram P L)
    [FiniteDomains g] (who : P)
    (σ : (pureKernelGame g).Profile)
    (s : (pureKernelGame g).Strategy who) : Prop :=
  (pureKernelGame g).IsBestResponse who σ s

/-- Pure strict Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureStrictNash [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pureKernelGame g).Profile) : Prop :=
  (pureKernelGame g).IsStrictNash σ

/-- Exact potential for the fixed-program Vegas strategic form. -/
def IsPureExactPotential [Fintype P] (g : WFProgram P L)
    [FiniteDomains g]
    (Φ : (pureKernelGame g).Profile → ℝ) : Prop :=
  (pureKernelGame g).IsExactPotential Φ

/-- Ordinal potential for the fixed-program Vegas strategic form. -/
def IsPureOrdinalPotential [Fintype P] (g : WFProgram P L)
    [FiniteDomains g]
    (Φ : (pureKernelGame g).Profile → ℝ) : Prop :=
  (pureKernelGame g).IsOrdinalPotential Φ

end Vegas
