import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties
import Vegas.Core.Finite
import Vegas.Strategic.KernelGame

/-!
# Fixed-Program Pure Strategic Form

This file defines the pure strategic form for a fixed Vegas program. Its
strategy carrier is the reachable legal pure-strategy space at the program's
finite syntax horizon.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Fixed-program pure game form whose outcomes are terminal public machine
states, before payoff projection. -/
noncomputable def purePublicStateGameForm [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P :=
  purePublicStateGameFormAt g

@[simp] theorem purePublicStateGameForm_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (purePublicStateGameForm g).Profile) :
    (purePublicStateGameForm g).outcomeKernel σ =
      purePublicStateOutcomeKernelAt g σ := rfl

/-- Fixed-program pure game form of a Vegas program, before utility is
attached. -/
noncomputable def pureGameForm [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.GameForm P :=
  pureGameFormAt g

@[simp] theorem pureGameForm_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pureGameForm g).Profile) :
    (pureGameForm g).outcomeKernel σ =
      pureOutcomeKernelAt g σ := rfl

/-- Fixed-program pure strategic form of a Vegas program.

The outcome kernel is `pureOutcomeKernelAt`. -/
noncomputable def pureKernelGame [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P :=
  pureKernelGameAt g

@[simp] theorem pureKernelGame_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pureKernelGame g).Profile) :
    (pureKernelGame g).outcomeKernel σ =
      pureOutcomeKernelAt g σ := rfl

@[simp] theorem pureKernelGame_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGame g).Strategy = pureStrategyAt g := rfl

/-- `pureKernelGame` is the finite pure strategic form of a checked Vegas
program. -/
theorem pureKernelGame_eu
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pureKernelGame g).Profile) (who : P) :
    (pureKernelGame g).eu σ who =
      (pureKernelGameAt g).eu σ who := rfl

@[simp] theorem pureKernelGame_toGameForm
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGame g).toGameForm = pureGameForm g := by
  rfl

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
