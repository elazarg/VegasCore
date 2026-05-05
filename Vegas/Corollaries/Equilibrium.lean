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
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g) :
    IsNash g σ ↔
      ∀ who, IsBestResponse g who σ (σ who) := by
  simpa [IsNash, IsBestResponse] using
    (KernelGame.isNash_iff_bestResponse
      (G := pmfBehavioralKernelGame g) σ)

theorem IsNash_iff_IsNashFor_eu
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g) :
    IsNash g σ ↔ IsNashFor g (euPref g) σ := by
  simpa [IsNash, IsNashFor, euPref] using
    (KernelGame.IsNash_iff_IsNashFor_eu
      (G := pmfBehavioralKernelGame g) σ)

theorem dominant_is_nash
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g)
    (hdom : ∀ who, IsDominant g who (σ who)) :
    IsNash g σ := by
  simpa [IsNash, IsDominant] using
    (KernelGame.dominant_is_nash
      (G := pmfBehavioralKernelGame g) σ hdom)

theorem isNash_iff_no_improving
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g) :
    IsNash g σ ↔
      ¬ ∃ (who : P) (s' : Strategy g who),
        eu g (Function.update σ who s') who > eu g σ who := by
  simpa [IsNash, eu, Strategy] using
    (KernelGame.isNash_iff_no_improving
      (G := pmfBehavioralKernelGame g) (σ := σ))

theorem IsStrictNash.isNash
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {σ : StrategyProfile g} (hstrict : IsStrictNash g σ) :
    IsNash g σ := by
  simpa [IsStrictNash, IsNash] using
    (KernelGame.IsStrictNash.isNash
      (G := pmfBehavioralKernelGame g) hstrict)

theorem nash_pure_isCorrelatedEq
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {σ : StrategyProfile g} (hN : IsNash g σ) :
    IsCorrelatedEq g (PMF.pure σ) := by
  simpa [IsNash, IsCorrelatedEq] using
    (KernelGame.nash_pure_isCorrelatedEq
      (G := pmfBehavioralKernelGame g) hN)

theorem nash_pure_isCoarseCorrelatedEq
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {σ : StrategyProfile g} (hN : IsNash g σ) :
    IsCoarseCorrelatedEq g (PMF.pure σ) := by
  simpa [IsNash, IsCoarseCorrelatedEq] using
    (KernelGame.nash_pure_isCoarseCorrelatedEq
      (G := pmfBehavioralKernelGame g) hN)

end Vegas
