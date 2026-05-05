import Vegas.Equilibrium
import GameTheory.Concepts.ApproximateNash
import GameTheory.Concepts.DominanceSolvability
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.SecurityStrategy
import GameTheory.Concepts.Minimax
import GameTheory.Concepts.PriceOfAnarchy

/-!
# Vegas game-theoretic properties

Core game-theoretic property definitions for finite Vegas programs, transported
through the PMF behavioral graph-machine FOSG kernel game.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

def IsεNash [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (ε : ℝ) (σ : StrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsεNash ε σ

def IsεBestResponse [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (ε : ℝ) (who : P) (σ : StrategyProfile g LF)
    (s : Strategy g LF who) : Prop :=
  (pmfBehavioralKernelGame g LF).IsεBestResponse ε who σ s

def Survives [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (n : ℕ) (who : P) (s : Strategy g LF who) : Prop :=
  (pmfBehavioralKernelGame g LF).Survives n who s

def IsRationalizable [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (s : Strategy g LF who) : Prop :=
  (pmfBehavioralKernelGame g LF).IsRationalizable who s

def IsIndividuallyRational [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (r : P → ℝ) (σ : StrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsIndividuallyRational r σ

def IsDominanceSolvable [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) : Prop :=
  (pmfBehavioralKernelGame g LF).IsDominanceSolvable

noncomputable def IsDominanceSolvable.dominantProfile [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (h : IsDominanceSolvable g LF) : StrategyProfile g LF :=
  KernelGame.IsDominanceSolvable.dominantProfile
    (G := pmfBehavioralKernelGame g LF) h

def IsExactPotential [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (Φ : StrategyProfile g LF → ℝ) : Prop :=
  (pmfBehavioralKernelGame g LF).IsExactPotential Φ

def IsOrdinalPotential [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (Φ : StrategyProfile g LF → ℝ) : Prop :=
  (pmfBehavioralKernelGame g LF).IsOrdinalPotential Φ

def Guarantees [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (s : Strategy g LF who) (v : ℝ) : Prop :=
  (pmfBehavioralKernelGame g LF).Guarantees who s v

def IsSaddlePoint
    (g : WFProgram (Fin 2) L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsSaddlePoint σ

def MixedStrategy [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) (who : P) : Type :=
  PMF (Strategy g LF who)

def MixedStrategyProfile [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    [∀ who, Fintype (Strategy g LF who)] : Type :=
  KernelGame.Profile (pmfBehavioralKernelGame g LF).mixedExtension

def IsMixedNash [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    [∀ who, Fintype (Strategy g LF who)]
    (σ : MixedStrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).mixedExtension.IsNash σ

noncomputable def mixedEu [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    [∀ who, Fintype (Strategy g LF who)]
    (σ : MixedStrategyProfile g LF) (who : P) : ℝ :=
  (pmfBehavioralKernelGame g LF).mixedExtension.eu σ who

def IsConstantSum [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) (c : ℝ) : Prop :=
  (pmfBehavioralKernelGame g LF).IsConstantSum c

def IsZeroSum [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) : Prop :=
  (pmfBehavioralKernelGame g LF).IsZeroSum

def IsTeamGame [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) : Prop :=
  (pmfBehavioralKernelGame g LF).IsTeamGame

noncomputable def optimalWelfare [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) : ℝ :=
  (pmfBehavioralKernelGame g LF).optimalWelfare

end Vegas
