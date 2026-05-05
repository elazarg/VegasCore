import Vegas.PureStrategic
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.NashProperties
import GameTheory.Concepts.PotentialGame
import GameTheory.Theorems.NashExistence

/-!
# Pure-strategic corollaries

Corollaries for the finite graph-machine FOSG pure strategic form.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- If every player has a dominant pure strategy, then the finite FOSG pure
strategic form has a pure Nash equilibrium. -/
theorem pure_nash_of_all_have_dominant
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (h : ∀ who, ∃ s : (pureKernelGame g LF).Strategy who,
      IsPureDominant g LF who s) :
    ∃ σ : (pureKernelGame g LF).Profile, IsPureNash g LF σ := by
  simpa [IsPureDominant, IsPureNash] using
    (GameTheory.KernelGame.nash_of_all_have_dominant
      (G := pureKernelGame g LF) h)

/-- Pure Nash equilibrium is exactly everyone playing a pure best response. -/
theorem isPureNash_iff_bestResponse
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : (pureKernelGame g LF).Profile) :
    IsPureNash g LF σ ↔
      ∀ who, IsPureBestResponse g LF who σ (σ who) := by
  simpa [IsPureNash, IsPureBestResponse] using
    (GameTheory.KernelGame.isNash_iff_bestResponse
      (G := pureKernelGame g LF) σ)

/-- Any pure dominant strategy is a pure best response against every profile. -/
theorem pure_dominant_isBestResponse
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (s : (pureKernelGame g LF).Strategy who)
    (σ : (pureKernelGame g LF).Profile)
    (hdom : IsPureDominant g LF who s) :
    IsPureBestResponse g LF who σ s := by
  simpa [IsPureDominant, IsPureBestResponse] using
    (GameTheory.KernelGame.dominant_isBestResponse
      (G := pureKernelGame g LF) who s σ hdom)

/-- Pure Nash is equivalent to the absence of a strictly improving pure
unilateral deviation. -/
theorem isPureNash_iff_no_improving
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    {σ : (pureKernelGame g LF).Profile} :
    IsPureNash g LF σ ↔
      ¬ ∃ (who : P) (s' : (pureKernelGame g LF).Strategy who),
        (pureKernelGame g LF).eu (Function.update σ who s') who >
          (pureKernelGame g LF).eu σ who := by
  simpa [IsPureNash] using
    (GameTheory.KernelGame.isNash_iff_no_improving
      (G := pureKernelGame g LF) (σ := σ))

/-- Every exact potential on the finite FOSG pure strategic form is also an
ordinal potential. -/
theorem IsPureExactPotential.toOrdinal
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    {Φ : (pureKernelGame g LF).Profile → ℝ}
    (hΦ : IsPureExactPotential g LF Φ) :
    IsPureOrdinalPotential g LF Φ := by
  simpa [IsPureExactPotential, IsPureOrdinalPotential] using
    (GameTheory.KernelGame.IsExactPotential.toOrdinal
      (G := pureKernelGame g LF) hΦ)

/-- A global maximizer of an exact potential is a pure Nash equilibrium. -/
theorem IsPureExactPotential.nash_of_maximizer
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    {Φ : (pureKernelGame g LF).Profile → ℝ}
    (hΦ : IsPureExactPotential g LF Φ)
    {σ : (pureKernelGame g LF).Profile}
    (hmax : ∀ τ : (pureKernelGame g LF).Profile, Φ σ ≥ Φ τ) :
    IsPureNash g LF σ := by
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.IsExactPotential.nash_of_maximizer
      (G := pureKernelGame g LF) hΦ hmax)

/-- A global maximizer of an ordinal potential is a pure Nash equilibrium. -/
theorem IsPureOrdinalPotential.nash_of_maximizer
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    {Φ : (pureKernelGame g LF).Profile → ℝ}
    (hΦ : IsPureOrdinalPotential g LF Φ)
    {σ : (pureKernelGame g LF).Profile}
    (hmax : ∀ τ : (pureKernelGame g LF).Profile, Φ σ ≥ Φ τ) :
    IsPureNash g LF σ := by
  simpa [IsPureOrdinalPotential, IsPureNash] using
    (GameTheory.KernelGame.IsOrdinalPotential.nash_of_maximizer
      (G := pureKernelGame g LF) hΦ hmax)

/-- An exact potential on the finite FOSG pure strategic form guarantees a
pure Nash equilibrium under the usual finite/nonempty profile assumptions. -/
theorem pure_exact_potential_nash_exists
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    {Φ : (pureKernelGame g LF).Profile → ℝ}
    (hΦ : IsPureExactPotential g LF Φ)
    [Finite ((pureKernelGame g LF).Profile)]
    [Nonempty ((pureKernelGame g LF).Profile)] :
    ∃ σ : (pureKernelGame g LF).Profile, IsPureNash g LF σ := by
  haveI : Fintype ((pureKernelGame g LF).Profile) := Fintype.ofFinite _
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.exact_potential_nash_exists
      (G := pureKernelGame g LF) (Φ := Φ) hΦ)

end Vegas
