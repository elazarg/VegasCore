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
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsExactPotential g Φ) :
    IsOrdinalPotential g Φ := by
  simpa [IsExactPotential, IsOrdinalPotential] using
    (KernelGame.IsExactPotential.toOrdinal
      (G := pmfBehavioralKernelGame g) hΦ)

theorem IsExactPotential.nash_of_maximizer
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsExactPotential g Φ)
    {σ : StrategyProfile g}
    (hmax : ∀ τ : StrategyProfile g, Φ σ ≥ Φ τ) :
    IsNash g σ := by
  simpa [IsExactPotential, IsNash] using
    (KernelGame.IsExactPotential.nash_of_maximizer
      (G := pmfBehavioralKernelGame g) hΦ hmax)

theorem IsOrdinalPotential.nash_of_maximizer
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsOrdinalPotential g Φ)
    {σ : StrategyProfile g}
    (hmax : ∀ τ : StrategyProfile g, Φ σ ≥ Φ τ) :
    IsNash g σ := by
  simpa [IsOrdinalPotential, IsNash] using
    (KernelGame.IsOrdinalPotential.nash_of_maximizer
      (G := pmfBehavioralKernelGame g) hΦ hmax)

theorem exact_potential_nash_exists
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [Finite (StrategyProfile g)] [Nonempty (StrategyProfile g)]
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsExactPotential g Φ) :
    ∃ σ : StrategyProfile g, IsNash g σ := by
  let _ : Fintype (StrategyProfile g) := Fintype.ofFinite _
  simpa [IsExactPotential, IsNash] using
    (KernelGame.exact_potential_nash_exists
      (G := pmfBehavioralKernelGame g) hΦ)

theorem nash_of_all_have_dominant
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (h : ∀ who, ∃ s : Strategy g who, IsDominant g who s) :
    ∃ σ : StrategyProfile g, IsNash g σ := by
  simpa [IsDominant, IsNash] using
    (KernelGame.nash_of_all_have_dominant
      (G := pmfBehavioralKernelGame g) h)

theorem IsDominanceSolvable.isNash
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (h : IsDominanceSolvable g) :
    IsNash g (IsDominanceSolvable.dominantProfile g h) := by
  simpa [IsDominanceSolvable, IsNash,
    IsDominanceSolvable.dominantProfile] using
    (KernelGame.IsDominanceSolvable.isNash
      (G := pmfBehavioralKernelGame g) h)

theorem IsIndividuallyRational.mono
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {r r' : P → ℝ} {σ : StrategyProfile g}
    (hIR : IsIndividuallyRational g r σ)
    (hle : ∀ who, r' who ≤ r who) :
    IsIndividuallyRational g r' σ := by
  simpa [IsIndividuallyRational] using
    (KernelGame.IsIndividuallyRational.mono
      (G := pmfBehavioralKernelGame g) hIR hle)

theorem IsStrictNash.isRationalizable
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {σ : StrategyProfile g} (hN : IsNash g σ) (who : P) :
    IsRationalizable g who (σ who) := by
  simpa [IsNash, IsRationalizable] using
    (KernelGame.IsNash.isRationalizable
      (G := pmfBehavioralKernelGame g) hN who)

theorem IsTeamGame.socialWelfare_eq
    [Fintype P] [Inhabited P]
    (g : WFProgram P L) [FiniteDomains g]
    (hteam : IsTeamGame g) (σ : StrategyProfile g) (i : P) :
    socialWelfare g σ = Fintype.card P * eu g σ i := by
  simpa [IsTeamGame, socialWelfare, eu] using
    (KernelGame.IsTeamGame.socialWelfare_eq
      (G := pmfBehavioralKernelGame g) hteam σ i)

end Vegas
