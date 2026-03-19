import Vegas.Strategic
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.BestResponse
import GameTheory.Core.GameProperties

/-!
# Vegas equilibrium wrappers

Game-theoretic vocabulary for Vegas programs, defined by transport through the
`toKernelGame` strategic bridge.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Strategy profiles for a Vegas program are exactly the profiles of its
kernel-game image. -/
abbrev StrategyProfile (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) : Type :=
  KernelGame.Profile (toKernelGame p env hd)

/-- Nash equilibrium for a Vegas program, via `toKernelGame`. -/
def IsNash (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) : Prop :=
  (toKernelGame p env hd).IsNash σ

/-- Best response for a player in a Vegas program, via `toKernelGame`. -/
def IsBestResponse (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (σ : StrategyProfile p env hd)
    (s : (toKernelGame p env hd).Strategy who) : Prop :=
  (toKernelGame p env hd).IsBestResponse who σ s

/-- Dominant strategy for a player in a Vegas program, via `toKernelGame`. -/
def IsDominant (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s : (toKernelGame p env hd).Strategy who) : Prop :=
  (toKernelGame p env hd).IsDominant who s

/-- Pareto dominance for Vegas strategy profiles, via `toKernelGame`. -/
def ParetoDominates (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ τ : StrategyProfile p env hd) : Prop :=
  (toKernelGame p env hd).ParetoDominates σ τ

/-- Pareto efficiency for Vegas strategy profiles, via `toKernelGame`. -/
def IsParetoEfficient (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) : Prop :=
  (toKernelGame p env hd).IsParetoEfficient σ

/-- Social welfare of a Vegas strategy profile, via `toKernelGame`. -/
noncomputable def socialWelfare [Fintype P] (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) : ℝ :=
  (toKernelGame p env hd).socialWelfare σ

/-- Vegas Nash is equivalent to every player playing a Vegas best response. -/
theorem isNash_iff_bestResponse (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) :
    IsNash p env hd σ ↔ ∀ who, IsBestResponse p env hd who σ (σ who) := by
  simpa [IsNash, IsBestResponse] using
    (KernelGame.isNash_iff_bestResponse (G := toKernelGame p env hd) σ)

/-- A profile of Vegas-dominant strategies is a Vegas Nash equilibrium. -/
theorem dominant_is_nash (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd)
    (hdom : ∀ who, IsDominant p env hd who (σ who)) :
    IsNash p env hd σ := by
  simpa [IsNash, IsDominant] using
    (KernelGame.dominant_is_nash (G := toKernelGame p env hd) σ hdom)

/-- Vegas Nash is exactly preference-parameterized Nash with EU preference. -/
theorem IsNash_iff_IsNashFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) :
    IsNash p env hd σ ↔
      (toKernelGame p env hd).IsNashFor (toKernelGame p env hd).euPref σ := by
  simpa [IsNash] using
    (KernelGame.IsNash_iff_IsNashFor_eu (G := toKernelGame p env hd) σ)

end Vegas
