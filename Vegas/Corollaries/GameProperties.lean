import Vegas.GameProperties
import GameTheory.Concepts.DominanceSolvability
import GameTheory.Concepts.IndividualRationality
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.ZeroSum
import GameTheory.Concepts.ConstantSum
import GameTheory.Concepts.WelfareTheorems
import GameTheory.Theorems.NashExistence

/-!
# Vegas structural game-theory corollaries

Selected structural corollaries for the PMF behavioral graph-machine FOSG game.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

theorem IsExactPotential.toOrdinal
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    {Φ : StrategyProfile g LF → ℝ}
    (hΦ : IsExactPotential g LF Φ) :
    IsOrdinalPotential g LF Φ := by
  simpa [IsExactPotential, IsOrdinalPotential] using
    (KernelGame.IsExactPotential.toOrdinal
      (G := pmfBehavioralKernelGame g LF) hΦ)

theorem IsExactPotential.nash_of_maximizer
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    {Φ : StrategyProfile g LF → ℝ}
    (hΦ : IsExactPotential g LF Φ)
    {σ : StrategyProfile g LF}
    (hmax : ∀ τ : StrategyProfile g LF, Φ σ ≥ Φ τ) :
    IsNash g LF σ := by
  simpa [IsExactPotential, IsNash] using
    (KernelGame.IsExactPotential.nash_of_maximizer
      (G := pmfBehavioralKernelGame g LF) hΦ hmax)

theorem IsOrdinalPotential.nash_of_maximizer
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    {Φ : StrategyProfile g LF → ℝ}
    (hΦ : IsOrdinalPotential g LF Φ)
    {σ : StrategyProfile g LF}
    (hmax : ∀ τ : StrategyProfile g LF, Φ σ ≥ Φ τ) :
    IsNash g LF σ := by
  simpa [IsOrdinalPotential, IsNash] using
    (KernelGame.IsOrdinalPotential.nash_of_maximizer
      (G := pmfBehavioralKernelGame g LF) hΦ hmax)

theorem exact_potential_nash_exists
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    [Finite (StrategyProfile g LF)] [Nonempty (StrategyProfile g LF)]
    {Φ : StrategyProfile g LF → ℝ}
    (hΦ : IsExactPotential g LF Φ) :
    ∃ σ : StrategyProfile g LF, IsNash g LF σ := by
  let _ : Fintype (StrategyProfile g LF) := Fintype.ofFinite _
  simpa [IsExactPotential, IsNash] using
    (KernelGame.exact_potential_nash_exists
      (G := pmfBehavioralKernelGame g LF) hΦ)

theorem nash_of_all_have_dominant
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (h : ∀ who, ∃ s : Strategy g LF who, IsDominant g LF who s) :
    ∃ σ : StrategyProfile g LF, IsNash g LF σ := by
  simpa [IsDominant, IsNash] using
    (KernelGame.nash_of_all_have_dominant
      (G := pmfBehavioralKernelGame g LF) h)

theorem IsDominanceSolvable.isNash
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (h : IsDominanceSolvable g LF) :
    IsNash g LF (IsDominanceSolvable.dominantProfile g LF h) := by
  simpa [IsDominanceSolvable, IsNash,
    IsDominanceSolvable.dominantProfile] using
    (KernelGame.IsDominanceSolvable.isNash
      (G := pmfBehavioralKernelGame g LF) h)

theorem IsIndividuallyRational.mono
    [Fintype P] {g : WFProgram P L} {LF : FiniteValuation L}
    {r r' : P → ℝ} {σ : StrategyProfile g LF}
    (hIR : IsIndividuallyRational g LF r σ)
    (hle : ∀ who, r' who ≤ r who) :
    IsIndividuallyRational g LF r' σ := by
  simpa [IsIndividuallyRational] using
    (KernelGame.IsIndividuallyRational.mono
      (G := pmfBehavioralKernelGame g LF) hIR hle)

theorem IsStrictNash.isRationalizable
    [Fintype P] {g : WFProgram P L} {LF : FiniteValuation L}
    {σ : StrategyProfile g LF} (hN : IsNash g LF σ) (who : P) :
    IsRationalizable g LF who (σ who) := by
  simpa [IsNash, IsRationalizable] using
    (KernelGame.IsNash.isRationalizable
      (G := pmfBehavioralKernelGame g LF) hN who)

theorem IsTeamGame.socialWelfare_eq
    [Fintype P] [Inhabited P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (hteam : IsTeamGame g LF) (σ : StrategyProfile g LF) (i : P) :
    socialWelfare g LF σ = Fintype.card P * eu g LF σ i := by
  simpa [IsTeamGame, socialWelfare, eu] using
    (KernelGame.IsTeamGame.socialWelfare_eq
      (G := pmfBehavioralKernelGame g LF) hteam σ i)

end Vegas
