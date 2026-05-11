import Vegas.Strategic.Equilibrium
import GameTheory.Concepts.ApproximateNash
import GameTheory.Concepts.DominanceSolvability
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.SecurityStrategy
import GameTheory.Concepts.Minimax
import GameTheory.Concepts.PriceOfAnarchy

/-!
# Vegas game-theoretic properties

Core game-theoretic property definitions for finite Vegas programs, transported
through the native PMF behavioral event-graph machine kernel game.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

def IsεNash [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (ε : ℝ) (σ : StrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsεNash ε σ

def IsεBestResponse [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (ε : ℝ) (who : P) (σ : StrategyProfile g)
    (s : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).IsεBestResponse ε who σ s

def Survives [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (n : ℕ) (who : P) (s : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).Survives n who s

def IsRationalizable [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).IsRationalizable who s

def IsIndividuallyRational [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (r : P → ℝ) (σ : StrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsIndividuallyRational r σ

def IsDominanceSolvable [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : Prop :=
  (pmfBehavioralKernelGame g).IsDominanceSolvable

noncomputable def IsDominanceSolvable.dominantProfile [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (h : IsDominanceSolvable g) : StrategyProfile g :=
  KernelGame.IsDominanceSolvable.dominantProfile
    (G := pmfBehavioralKernelGame g) h

def IsExactPotential [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (Φ : StrategyProfile g → ℝ) : Prop :=
  (pmfBehavioralKernelGame g).IsExactPotential Φ

def IsOrdinalPotential [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (Φ : StrategyProfile g → ℝ) : Prop :=
  (pmfBehavioralKernelGame g).IsOrdinalPotential Φ

def Guarantees [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s : Strategy g who) (v : ℝ) : Prop :=
  (pmfBehavioralKernelGame g).Guarantees who s v

def IsSaddlePoint
    (g : WFProgram (Fin 2) L) [FiniteDomains g]
    (σ : StrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsSaddlePoint σ

def MixedStrategy [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] (who : P) : Type :=
  PMF (Strategy g who)

def MixedStrategyProfile [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : Type :=
  KernelGame.Profile (pmfBehavioralKernelGame g).mixedExtension

def IsMixedNash [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (σ : MixedStrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).mixedExtension.IsNash σ

noncomputable def mixedEu [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (σ : MixedStrategyProfile g) (who : P) : ℝ :=
  (pmfBehavioralKernelGame g).mixedExtension.eu σ who

def IsConstantSum [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] (c : ℝ) : Prop :=
  (pmfBehavioralKernelGame g).IsConstantSum c

def IsZeroSum [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : Prop :=
  (pmfBehavioralKernelGame g).IsZeroSum

def IsTeamGame [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : Prop :=
  (pmfBehavioralKernelGame g).IsTeamGame

noncomputable def optimalWelfare [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : ℝ :=
  (pmfBehavioralKernelGame g).optimalWelfare

noncomputable def bestNashWelfare [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    [Finite (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) : ℝ := by
  letI : Fintype (StrategyProfile g) := Fintype.ofFinite _
  exact (pmfBehavioralKernelGame g).bestNashWelfare (by
    simpa [IsNash] using hN)

noncomputable def worstNashWelfare [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    [Finite (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) : ℝ := by
  letI : Fintype (StrategyProfile g) := Fintype.ofFinite _
  exact (pmfBehavioralKernelGame g).worstNashWelfare (by
    simpa [IsNash] using hN)

end Vegas
