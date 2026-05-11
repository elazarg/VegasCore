import Vegas.Strategic.Properties
import GameTheory.Concepts.DominanceSolvability
import GameTheory.Concepts.IndividualRationality
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.ZeroSum
import GameTheory.Concepts.ConstantSum
import GameTheory.Concepts.WelfareTheorems
import GameTheory.Theorems.NashExistence
import GameTheory.Theorems.NashExistenceMixed
import GameTheory.Theorems.CorrelatedEqExistence

/-!
# Vegas structural game-theory corollaries

Selected structural corollaries for the PMF behavioral event-graph kernel game.
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

theorem worstNashWelfare_le_bestNashWelfare
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [Finite (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) :
    worstNashWelfare g hN ≤ bestNashWelfare g hN := by
  letI : Fintype (StrategyProfile g) := Fintype.ofFinite _
  simpa [worstNashWelfare, bestNashWelfare, IsNash] using
    (KernelGame.worstNashWelfare_le_bestNashWelfare
      (G := pmfBehavioralKernelGame g)
      (by simpa [IsNash] using hN))

theorem bestNashWelfare_le_optimalWelfare
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [Finite (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ)
    (hbdd : BddAbove (Set.range (fun τ : StrategyProfile g => socialWelfare g τ))) :
    bestNashWelfare g hN ≤ optimalWelfare g := by
  letI : Fintype (StrategyProfile g) := Fintype.ofFinite _
  have hbdd' :
      BddAbove
        (Set.range (fun τ : (pmfBehavioralKernelGame g).Profile =>
          (pmfBehavioralKernelGame g).socialWelfare τ)) := by
    exact hbdd
  simpa [bestNashWelfare, optimalWelfare, socialWelfare, IsNash] using
    (KernelGame.bestNashWelfare_le_optimalWelfare
      (G := pmfBehavioralKernelGame g)
      (by simpa [IsNash] using hN)
      hbdd')

theorem mixedNash_exists
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Finite (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Finite (Outcome P)] :
    ∃ σ : MixedStrategyProfile g, IsMixedNash g σ := by
  letI : ∀ who, Finite ((pmfBehavioralKernelGame g).Strategy who) := by
    intro who
    change Finite (Strategy g who)
    infer_instance
  letI : Finite (pmfBehavioralKernelGame g).Outcome := by
    change Finite (Outcome P)
    infer_instance
  simpa [MixedStrategyProfile, IsMixedNash] using
    (KernelGame.mixed_nash_exists (pmfBehavioralKernelGame g))

theorem mixedNash_exists_of_bounded
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Finite (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    {C : P → ℝ}
    (hbd : ∀ who outcome,
      |(pmfBehavioralKernelGame g).utility outcome who| ≤ C who) :
    ∃ σ : MixedStrategyProfile g, IsMixedNash g σ := by
  letI : ∀ who, Finite ((pmfBehavioralKernelGame g).Strategy who) := by
    intro who
    change Finite (Strategy g who)
    infer_instance
  simpa [MixedStrategyProfile, IsMixedNash] using
    (KernelGame.mixed_nash_exists_of_bounded (pmfBehavioralKernelGame g) hbd)

theorem pureBlockedTraceKernelGameAt_utility_bounded
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    ∃ C : P → ℝ, ∀ who trace,
      |(pureBlockedTraceKernelGameAt g).utility trace who| ≤ C who := by
  classical
  refine ⟨fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun state : (eventGraphMachine g).State =>
        (pureBlockedTraceKernelGameAt g).utility ([], state) who)).choose, ?_⟩
  intro who trace
  simpa [pureBlockedTraceKernelGameAt, syntaxBlockedTraceUtility] using
    (Math.Probability.exists_abs_bound_of_finite
      (fun state : (eventGraphMachine g).State =>
        (pureBlockedTraceKernelGameAt g).utility ([], state) who)).choose_spec trace.2

theorem pureBlockedTrace_mixedNash_exists
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Nonempty ((pureBlockedTraceKernelGameAt g).Strategy who)] :
    ∃ σ : ∀ who, PMF ((pureBlockedTraceKernelGameAt g).Strategy who),
      (pureBlockedTraceKernelGameAt g).mixedExtension.IsNash σ := by
  classical
  letI : ∀ who, Fintype ((pureBlockedTraceKernelGameAt g).Strategy who) := by
    intro who
    change Fintype (pureStrategyAt g who)
    infer_instance
  obtain ⟨C, hbd⟩ := pureBlockedTraceKernelGameAt_utility_bounded g
  exact KernelGame.mixed_nash_exists_of_bounded (pureBlockedTraceKernelGameAt g) hbd

theorem correlatedEq_exists
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Finite (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Finite (Outcome P)] :
    ∃ μ : CorrelatedProfile g, IsCorrelatedEq g μ := by
  letI : ∀ who, Finite ((pmfBehavioralKernelGame g).Strategy who) := by
    intro who
    change Finite (Strategy g who)
    infer_instance
  letI : Finite (pmfBehavioralKernelGame g).Outcome := by
    change Finite (Outcome P)
    infer_instance
  simpa [CorrelatedProfile, StrategyProfile, IsCorrelatedEq] using
    (KernelGame.correlatedEq_exists (pmfBehavioralKernelGame g))

theorem correlatedEq_exists_of_bounded
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Finite (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    {C : P → ℝ}
    (hbd : ∀ who outcome,
      |(pmfBehavioralKernelGame g).utility outcome who| ≤ C who) :
    ∃ μ : CorrelatedProfile g, IsCorrelatedEq g μ := by
  letI : ∀ who, Finite ((pmfBehavioralKernelGame g).Strategy who) := by
    intro who
    change Finite (Strategy g who)
    infer_instance
  obtain ⟨σ, hN⟩ :=
    KernelGame.mixed_nash_exists_of_bounded (pmfBehavioralKernelGame g) hbd
  exact ⟨Math.PMFProduct.pmfPi σ, by
    simpa [CorrelatedProfile, StrategyProfile, IsCorrelatedEq] using
      (KernelGame.mixed_nash_isCorrelatedEq_of_bounded
        (G := pmfBehavioralKernelGame g) σ hN hbd)⟩

theorem coarseCorrelatedEq_exists
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Finite (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Finite (Outcome P)] :
    ∃ μ : CorrelatedProfile g, IsCoarseCorrelatedEq g μ := by
  letI : ∀ who, Finite ((pmfBehavioralKernelGame g).Strategy who) := by
    intro who
    change Finite (Strategy g who)
    infer_instance
  letI : Finite (pmfBehavioralKernelGame g).Outcome := by
    change Finite (Outcome P)
    infer_instance
  simpa [CorrelatedProfile, StrategyProfile, IsCoarseCorrelatedEq] using
    (KernelGame.coarseCorrelatedEq_exists (pmfBehavioralKernelGame g))

theorem coarseCorrelatedEq_exists_of_bounded
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Finite (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    {C : P → ℝ}
    (hbd : ∀ who outcome,
      |(pmfBehavioralKernelGame g).utility outcome who| ≤ C who) :
    ∃ μ : CorrelatedProfile g, IsCoarseCorrelatedEq g μ := by
  letI : ∀ who, Finite ((pmfBehavioralKernelGame g).Strategy who) := by
    intro who
    change Finite (Strategy g who)
    infer_instance
  obtain ⟨σ, hN⟩ :=
    KernelGame.mixed_nash_exists_of_bounded (pmfBehavioralKernelGame g) hbd
  exact ⟨Math.PMFProduct.pmfPi σ, by
    simpa [CorrelatedProfile, StrategyProfile, IsCoarseCorrelatedEq] using
      (KernelGame.mixed_nash_isCoarseCorrelatedEq_of_bounded
        (G := pmfBehavioralKernelGame g) σ hN hbd)⟩

end Vegas
