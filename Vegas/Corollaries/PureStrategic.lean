import Vegas.PureStrategic
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.NashProperties
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.PotentialFIP
import GameTheory.Theorems.NashExistence

/-!
# Vegas pure-strategic corollaries

Corollaries for the fixed-program pure strategic form.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- If every player has a dominant pure strategy for the fixed program,
then the program has a pure Nash equilibrium. -/
theorem pure_nash_of_all_have_dominant (g : WFProgram P L)
    (h : ∀ who, ∃ s : FeasibleProgramPureStrategy g who,
      IsPureDominant g who s) :
    ∃ σ : FeasibleProgramPureProfile g, IsPureNash g σ := by
  simpa [IsPureDominant, IsPureNash] using
    (GameTheory.KernelGame.nash_of_all_have_dominant
      (G := pureKernelGame g) h)

/-- Pure Nash equilibrium is exactly everyone playing a pure best response. -/
theorem isPureNash_iff_bestResponse (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) :
    IsPureNash g σ ↔ ∀ who, IsPureBestResponse g who σ (σ who) := by
  simpa [IsPureNash, IsPureBestResponse] using
    (GameTheory.KernelGame.isNash_iff_bestResponse
      (G := pureKernelGame g) σ)

/-- Any pure dominant strategy is a pure best response against every profile. -/
theorem pure_dominant_isBestResponse (g : WFProgram P L)
    (who : P) (s : FeasibleProgramPureStrategy g who)
    (σ : FeasibleProgramPureProfile g)
    (hdom : IsPureDominant g who s) :
    IsPureBestResponse g who σ s := by
  simpa [IsPureDominant, IsPureBestResponse] using
    (GameTheory.KernelGame.dominant_isBestResponse
      (G := pureKernelGame g) who s σ hdom)

/-- In the fixed-program pure strategic form, pure Nash is equivalent to there
being no strictly improving pure unilateral deviation. -/
theorem isPureNash_iff_no_improving (g : WFProgram P L)
    {σ : FeasibleProgramPureProfile g} :
    IsPureNash g σ ↔
      ¬ ∃ (who : P) (s' : FeasibleProgramPureStrategy g who),
        (pureKernelGame g).eu (Function.update σ who s') who >
          (pureKernelGame g).eu σ who := by
  simpa [IsPureNash] using
    (GameTheory.KernelGame.isNash_iff_no_improving
      (G := pureKernelGame g) (σ := σ))

/-- Replacing a pure Nash action with another pure best response preserves the
deviator's expected utility. -/
theorem pure_nash_update_bestResponse_eu_eq (g : WFProgram P L)
    {σ : FeasibleProgramPureProfile g}
    (hN : IsPureNash g σ)
    {who : P} {s' : FeasibleProgramPureStrategy g who}
    (hbr : IsPureBestResponse g who σ s') :
    (pureKernelGame g).eu (Function.update σ who s') who =
      (pureKernelGame g).eu σ who := by
  simpa [IsPureNash, IsPureBestResponse] using
    (GameTheory.KernelGame.isNash_update_bestResponse
      (G := pureKernelGame g) hN hbr)

/-- Every exact potential on the fixed-program pure strategic form is also an
ordinal potential. -/
theorem IsPureExactPotential.toOrdinal (g : WFProgram P L)
    {Φ : FeasibleProgramPureProfile g → ℝ}
    (hΦ : IsPureExactPotential g Φ) :
    IsPureOrdinalPotential g Φ := by
  simpa [IsPureExactPotential, IsPureOrdinalPotential] using
    (GameTheory.KernelGame.IsExactPotential.toOrdinal
      (G := pureKernelGame g) hΦ)

/-- A global maximizer of an exact potential is a pure Nash equilibrium. -/
theorem IsPureExactPotential.nash_of_maximizer (g : WFProgram P L)
    {Φ : FeasibleProgramPureProfile g → ℝ}
    (hΦ : IsPureExactPotential g Φ)
    {σ : FeasibleProgramPureProfile g}
    (hmax : ∀ τ : FeasibleProgramPureProfile g, Φ σ ≥ Φ τ) :
    IsPureNash g σ := by
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.IsExactPotential.nash_of_maximizer
      (G := pureKernelGame g) hΦ hmax)

/-- A global maximizer of an ordinal potential is a pure Nash equilibrium. -/
theorem IsPureOrdinalPotential.nash_of_maximizer (g : WFProgram P L)
    {Φ : FeasibleProgramPureProfile g → ℝ}
    (hΦ : IsPureOrdinalPotential g Φ)
    {σ : FeasibleProgramPureProfile g}
    (hmax : ∀ τ : FeasibleProgramPureProfile g, Φ σ ≥ Φ τ) :
    IsPureNash g σ := by
  simpa [IsPureOrdinalPotential, IsPureNash] using
    (GameTheory.KernelGame.IsOrdinalPotential.nash_of_maximizer
      (G := pureKernelGame g) hΦ hmax)

/-- A strict global maximizer of an exact potential is a pure strict Nash
equilibrium. -/
theorem IsPureExactPotential.strictNash_of_strict_maximizer (g : WFProgram P L)
    {Φ : FeasibleProgramPureProfile g → ℝ}
    (hΦ : IsPureExactPotential g Φ)
    {σ : FeasibleProgramPureProfile g}
    (hmax : ∀ τ : FeasibleProgramPureProfile g, τ ≠ σ → Φ σ > Φ τ) :
    IsPureStrictNash g σ := by
  intro who s' hs'
  have hpot := hΦ who σ s'
  have hne : Function.update σ who s' ≠ σ := by
    intro h
    apply hs'
    have := congr_fun h who
    simpa [Function.update] using this
  have hlt := hmax _ hne
  simp only [pureKernelGame_Strategy] at hpot ⊢
  linarith

/-- In the fixed-program pure strategic form, exact-potential Nash equilibria
are exactly the local maximizers of the potential. -/
theorem IsPureExactPotential.isNash_iff_local_maximizer (g : WFProgram P L)
    {Φ : FeasibleProgramPureProfile g → ℝ}
    (hΦ : IsPureExactPotential g Φ)
    {σ : FeasibleProgramPureProfile g} :
    IsPureNash g σ ↔
      ∀ who (s' : FeasibleProgramPureStrategy g who),
        Φ σ ≥ Φ (Function.update σ who s') := by
  constructor
  · intro hN who s'
    have hpot := hΦ who σ s'
    have hge := hN who s'
    simp only [pureKernelGame_Strategy] at hpot hge ⊢
    linarith
  · intro hmax who s'
    have hpot := hΦ who σ s'
    have hge := hmax who s'
    simp only [pureKernelGame_Strategy] at hpot hge ⊢
    linarith

/-- In the fixed-program pure strategic form, ordinal-potential Nash
equilibria are exactly the local maximizers of the potential. -/
theorem IsPureOrdinalPotential.isNash_iff_local_maximizer (g : WFProgram P L)
    {Φ : FeasibleProgramPureProfile g → ℝ}
    (hΦ : IsPureOrdinalPotential g Φ)
    {σ : FeasibleProgramPureProfile g} :
    IsPureNash g σ ↔
      ∀ who (s' : FeasibleProgramPureStrategy g who),
        Φ σ ≥ Φ (Function.update σ who s') := by
  simpa [IsPureOrdinalPotential, IsPureNash] using
    (GameTheory.KernelGame.IsOrdinalPotential.isNash_iff_local_maximizer
      (G := pureKernelGame g) hΦ (σ := σ))

/-- An exact potential on the fixed-program pure strategic form guarantees a
pure Nash equilibrium, provided the pure profile space is finite and nonempty.
The `[Fintype …]` / `[Nonempty …]` instance parameters carry the finiteness
and nonemptiness of the *legal* profile space; users supply these from the
context-specific structure of their program. -/
theorem pure_exact_potential_nash_exists (g : WFProgram P L)
    {Φ : FeasibleProgramPureProfile g → ℝ}
    (hΦ : IsPureExactPotential g Φ)
    [Finite (FeasibleProgramPureProfile g)]
    [Nonempty (FeasibleProgramPureProfile g)] :
    ∃ σ : FeasibleProgramPureProfile g, IsPureNash g σ := by
  haveI : Fintype (FeasibleProgramPureProfile g) := Fintype.ofFinite _
  haveI : Fintype ((pureKernelGame g).Profile) :=
    inferInstanceAs (Fintype (FeasibleProgramPureProfile g))
  haveI : Nonempty ((pureKernelGame g).Profile) :=
    inferInstanceAs (Nonempty (FeasibleProgramPureProfile g))
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.exact_potential_nash_exists
      (G := pureKernelGame g) (Φ := Φ) hΦ)

end Vegas
