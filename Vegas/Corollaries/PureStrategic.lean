import Vegas.Strategic.Pure
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.NashProperties
import GameTheory.Concepts.PotentialGame
import GameTheory.Theorems.NashExistence

/-!
# Pure-strategic corollaries

Corollaries for the finite event-graph machine FOSG pure strategic form.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- If every player has a dominant pure strategy, then the finite FOSG pure
strategic form has a pure Nash equilibrium. -/
theorem pure_nash_of_all_have_dominant
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (h : ∀ who, ∃ s : (pureKernelGame g).Strategy who,
      IsPureDominant g who s) :
    ∃ σ : (pureKernelGame g).Profile, IsPureNash g σ := by
  simpa [IsPureDominant, IsPureNash] using
    (GameTheory.KernelGame.nash_of_all_have_dominant
      (G := pureKernelGame g) h)

/-- Pure Nash equilibrium is exactly everyone playing a pure best response. -/
theorem isPureNash_iff_bestResponse
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pureKernelGame g).Profile) :
    IsPureNash g σ ↔
      ∀ who, IsPureBestResponse g who σ (σ who) := by
  simpa [IsPureNash, IsPureBestResponse] using
    (GameTheory.KernelGame.isNash_iff_bestResponse
      (G := pureKernelGame g) σ)

/-- Any pure dominant strategy is a pure best response against every profile. -/
theorem pure_dominant_isBestResponse
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s : (pureKernelGame g).Strategy who)
    (σ : (pureKernelGame g).Profile)
    (hdom : IsPureDominant g who s) :
    IsPureBestResponse g who σ s := by
  simpa [IsPureDominant, IsPureBestResponse] using
    (GameTheory.KernelGame.dominant_isBestResponse
      (G := pureKernelGame g) who s σ hdom)

/-- Pure Nash is equivalent to the absence of a strictly improving pure
unilateral deviation. -/
theorem isPureNash_iff_no_improving
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {σ : (pureKernelGame g).Profile} :
    IsPureNash g σ ↔
      ¬ ∃ (who : P) (s' : (pureKernelGame g).Strategy who),
        (pureKernelGame g).eu (Function.update σ who s') who >
          (pureKernelGame g).eu σ who := by
  simpa [IsPureNash] using
    (GameTheory.KernelGame.isNash_iff_no_improving
      (G := pureKernelGame g) (σ := σ))

/-- Every exact potential on the finite FOSG pure strategic form is also an
ordinal potential. -/
theorem IsPureExactPotential.toOrdinal
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Φ : (pureKernelGame g).Profile → ℝ}
    (hΦ : IsPureExactPotential g Φ) :
    IsPureOrdinalPotential g Φ := by
  simpa [IsPureExactPotential, IsPureOrdinalPotential] using
    (GameTheory.KernelGame.IsExactPotential.toOrdinal
      (G := pureKernelGame g) hΦ)

/-- A global maximizer of an exact potential is a pure Nash equilibrium. -/
theorem IsPureExactPotential.nash_of_maximizer
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Φ : (pureKernelGame g).Profile → ℝ}
    (hΦ : IsPureExactPotential g Φ)
    {σ : (pureKernelGame g).Profile}
    (hmax : ∀ τ : (pureKernelGame g).Profile, Φ σ ≥ Φ τ) :
    IsPureNash g σ := by
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.IsExactPotential.nash_of_maximizer
      (G := pureKernelGame g) hΦ hmax)

/-- A global maximizer of an ordinal potential is a pure Nash equilibrium. -/
theorem IsPureOrdinalPotential.nash_of_maximizer
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Φ : (pureKernelGame g).Profile → ℝ}
    (hΦ : IsPureOrdinalPotential g Φ)
    {σ : (pureKernelGame g).Profile}
    (hmax : ∀ τ : (pureKernelGame g).Profile, Φ σ ≥ Φ τ) :
    IsPureNash g σ := by
  simpa [IsPureOrdinalPotential, IsPureNash] using
    (GameTheory.KernelGame.IsOrdinalPotential.nash_of_maximizer
      (G := pureKernelGame g) hΦ hmax)

/-- An exact potential on the finite FOSG pure strategic form guarantees a
pure Nash equilibrium under the usual finite/nonempty profile assumptions. -/
theorem pure_exact_potential_nash_exists
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Φ : (pureKernelGame g).Profile → ℝ}
    (hΦ : IsPureExactPotential g Φ)
    [Finite ((pureKernelGame g).Profile)]
    [Nonempty ((pureKernelGame g).Profile)] :
    ∃ σ : (pureKernelGame g).Profile, IsPureNash g σ := by
  haveI : Fintype ((pureKernelGame g).Profile) := Fintype.ofFinite _
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.exact_potential_nash_exists
      (G := pureKernelGame g) (Φ := Φ) hΦ)

end Vegas
