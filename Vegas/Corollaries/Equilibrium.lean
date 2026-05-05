import Vegas.Equilibrium
import Vegas.GameProperties
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.NashProperties
import GameTheory.Concepts.NashCorrelatedEq

/-!
# Equilibrium Corollaries

Basic equilibrium facts for the PMF behavioral graph-machine FOSG game.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

theorem isNash_iff_bestResponse
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) :
    IsNash g LF σ ↔
      ∀ who, IsBestResponse g LF who σ (σ who) := by
  simpa [IsNash, IsBestResponse] using
    (KernelGame.isNash_iff_bestResponse
      (G := pmfBehavioralKernelGame g LF) σ)

theorem IsNash_iff_IsNashFor_eu
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) :
    IsNash g LF σ ↔ IsNashFor g LF (euPref g LF) σ := by
  simpa [IsNash, IsNashFor, euPref] using
    (KernelGame.IsNash_iff_IsNashFor_eu
      (G := pmfBehavioralKernelGame g LF) σ)

theorem dominant_is_nash
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF)
    (hdom : ∀ who, IsDominant g LF who (σ who)) :
    IsNash g LF σ := by
  simpa [IsNash, IsDominant] using
    (KernelGame.dominant_is_nash
      (G := pmfBehavioralKernelGame g LF) σ hdom)

theorem isNash_iff_no_improving
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) :
    IsNash g LF σ ↔
      ¬ ∃ (who : P) (s' : Strategy g LF who),
        eu g LF (Function.update σ who s') who > eu g LF σ who := by
  simpa [IsNash, eu, Strategy] using
    (KernelGame.isNash_iff_no_improving
      (G := pmfBehavioralKernelGame g LF) (σ := σ))

theorem IsStrictNash.isNash
    [Fintype P] {g : WFProgram P L} {LF : FiniteValuation L}
    {σ : StrategyProfile g LF} (hstrict : IsStrictNash g LF σ) :
    IsNash g LF σ := by
  simpa [IsStrictNash, IsNash] using
    (KernelGame.IsStrictNash.isNash
      (G := pmfBehavioralKernelGame g LF) hstrict)

theorem nash_pure_isCorrelatedEq
    [Fintype P] {g : WFProgram P L} {LF : FiniteValuation L}
    {σ : StrategyProfile g LF} (hN : IsNash g LF σ) :
    IsCorrelatedEq g LF (PMF.pure σ) := by
  simpa [IsNash, IsCorrelatedEq] using
    (KernelGame.nash_pure_isCorrelatedEq
      (G := pmfBehavioralKernelGame g LF) hN)

theorem nash_pure_isCoarseCorrelatedEq
    [Fintype P] {g : WFProgram P L} {LF : FiniteValuation L}
    {σ : StrategyProfile g LF} (hN : IsNash g LF σ) :
    IsCoarseCorrelatedEq g LF (PMF.pure σ) := by
  simpa [IsNash, IsCoarseCorrelatedEq] using
    (KernelGame.nash_pure_isCoarseCorrelatedEq
      (G := pmfBehavioralKernelGame g LF) hN)

end Vegas
