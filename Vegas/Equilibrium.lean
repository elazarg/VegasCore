import Vegas.Strategic
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties

/-!
# Vegas equilibrium wrappers

behavioralKernelGame-theoretic vocabulary for Vegas programs, defined by transport through the
checked graph machine. The entire user-facing game-theory API consumes a
`WFProgram` bundle rather than a raw `(program, env, NormalizedDists)` triplet:
the bundle carries the full well-formedness obligations (`WFCtx`, `WF`,
`NormalizedDists`, `Legal`) needed to ensure a coherent game interpretation.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Strategy profiles for a Vegas program are exactly the profiles of its
kernel-game image. -/
def StrategyProfile (g : WFProgram P L) : Type :=
  KernelGame.Profile (behavioralKernelGame g)

/-- A single player's Vegas strategy is the corresponding strategy in the
kernel-game image. -/
def Strategy (g : WFProgram P L) (who : P) : Type :=
  (behavioralKernelGame g).Strategy who

/-- Correlated profiles for a Vegas program are profile distributions on its
strategy-profile space. -/
def CorrelatedProfile (g : WFProgram P L) : Type :=
  PMF (StrategyProfile g)

instance instFintypeGameStrategy (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)] :
    ∀ who, Fintype ((behavioralKernelGame g).Strategy who) := by
  intro who
  let I : Fintype (Strategy g who) := inferInstance
  simpa [Strategy] using I

instance instNonemptyGameStrategy (g : WFProgram P L)
    [∀ who, Nonempty (Strategy g who)] :
    ∀ who, Nonempty ((behavioralKernelGame g).Strategy who) := by
  intro who
  let I : Nonempty (Strategy g who) := inferInstance
  simpa [Strategy] using I

instance instFintypeGameProfile (g : WFProgram P L)
    [Fintype (StrategyProfile g)] :
    Fintype (KernelGame.Profile (behavioralKernelGame g)) := by
  let I : Fintype (StrategyProfile g) := inferInstance
  simpa [StrategyProfile] using I

instance instNonemptyGameProfile (g : WFProgram P L)
    [Nonempty (StrategyProfile g)] :
    Nonempty (KernelGame.Profile (behavioralKernelGame g)) := by
  let I : Nonempty (StrategyProfile g) := inferInstance
  simpa [StrategyProfile] using I

/-- Expected utility for a Vegas strategy profile. -/
noncomputable def eu (g : WFProgram P L)
    (σ : StrategyProfile g) (who : P) : ℝ :=
  (behavioralKernelGame g).eu σ who

/-- Correlated expected utility for a Vegas correlated profile. -/
noncomputable def correlatedEu (g : WFProgram P L)
    (μ : CorrelatedProfile g) (who : P) : ℝ :=
  (behavioralKernelGame g).correlatedEu μ who

/-- EU weak preference on Vegas outcome distributions. -/
def euPref (g : WFProgram P L) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (behavioralKernelGame g).euPref

/-- EU strict preference on Vegas outcome distributions. -/
def euStrictPref (g : WFProgram P L) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (behavioralKernelGame g).euStrictPref

/-- Nash equilibrium for a Vegas program. -/
def IsNash (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (behavioralKernelGame g).IsNash σ

/-- Preference-parameterized Nash equilibrium for a Vegas program. -/
def IsNashFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (behavioralKernelGame g).IsNashFor pref σ

/-- Best response for a player in a Vegas program. -/
def IsBestResponse (g : WFProgram P L)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (behavioralKernelGame g).IsBestResponse who σ s

/-- Preference-parameterized best response for a player in a Vegas program. -/
def IsBestResponseFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (behavioralKernelGame g).IsBestResponseFor pref who σ s

/-- Dominant strategy for a player in a Vegas program. -/
def IsDominant (g : WFProgram P L) (who : P) (s : Strategy g who) : Prop :=
  (behavioralKernelGame g).IsDominant who s

/-- Preference-parameterized dominant strategy for a player in a Vegas program. -/
def IsDominantFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy g who) : Prop :=
  (behavioralKernelGame g).IsDominantFor pref who s

/-- Strict Nash equilibrium for a Vegas program. -/
def IsStrictNash (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (behavioralKernelGame g).IsStrictNash σ

/-- Preference-parameterized strict Nash equilibrium for a Vegas program. -/
def IsStrictNashFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (behavioralKernelGame g).IsStrictNashFor spref σ

/-- Strictly dominant strategy for a player in a Vegas program. -/
def IsStrictDominant (g : WFProgram P L)
    (who : P) (s : Strategy g who) : Prop :=
  (behavioralKernelGame g).IsStrictDominant who s

/-- Preference-parameterized strictly dominant strategy for a Vegas player. -/
def IsStrictDominantFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy g who) : Prop :=
  (behavioralKernelGame g).IsStrictDominantFor spref who s

/-- Weak dominance between two Vegas strategies for one player. -/
def WeaklyDominates (g : WFProgram P L)
    (who : P) (s t : Strategy g who) : Prop :=
  (behavioralKernelGame g).WeaklyDominates who s t

/-- Preference-parameterized weak dominance between two Vegas strategies. -/
def WeaklyDominatesFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s t : Strategy g who) : Prop :=
  (behavioralKernelGame g).WeaklyDominatesFor pref who s t

/-- Strict dominance between two Vegas strategies for one player. -/
def StrictlyDominates (g : WFProgram P L)
    (who : P) (s t : Strategy g who) : Prop :=
  (behavioralKernelGame g).StrictlyDominates who s t

/-- Preference-parameterized strict dominance between two Vegas strategies. -/
def StrictlyDominatesFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s t : Strategy g who) : Prop :=
  (behavioralKernelGame g).StrictlyDominatesFor spref who s t

/-- Pareto dominance for Vegas strategy profiles. -/
def ParetoDominates (g : WFProgram P L) (σ τ : StrategyProfile g) : Prop :=
  (behavioralKernelGame g).ParetoDominates σ τ

/-- Preference-parameterized Pareto dominance for Vegas strategy profiles. -/
def ParetoDominatesFor (g : WFProgram P L)
    (pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ τ : StrategyProfile g) : Prop :=
  (behavioralKernelGame g).ParetoDominatesFor pref spref σ τ

/-- Pareto efficiency for Vegas strategy profiles. -/
def IsParetoEfficient (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (behavioralKernelGame g).IsParetoEfficient σ

/-- Preference-parameterized Pareto efficiency for Vegas strategy profiles. -/
def IsParetoEfficientFor (g : WFProgram P L)
    (pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (behavioralKernelGame g).IsParetoEfficientFor pref spref σ

/-- Social welfare of a Vegas strategy profile. -/
noncomputable def socialWelfare [Fintype P] (g : WFProgram P L)
    (σ : StrategyProfile g) : ℝ :=
  (behavioralKernelGame g).socialWelfare σ

/-- Correlated equilibrium for a Vegas correlated profile. -/
def IsCorrelatedEq (g : WFProgram P L) (μ : CorrelatedProfile g) : Prop :=
  (behavioralKernelGame g).IsCorrelatedEq μ

/-- Coarse correlated equilibrium for a Vegas correlated profile. -/
def IsCoarseCorrelatedEq (g : WFProgram P L) (μ : CorrelatedProfile g) : Prop :=
  (behavioralKernelGame g).IsCoarseCorrelatedEq μ

/-- Preference-parameterized correlated equilibrium for a Vegas correlated
profile. -/
def IsCorrelatedEqFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (μ : CorrelatedProfile g) : Prop :=
  (behavioralKernelGame g).IsCorrelatedEqFor pref μ

/-- Preference-parameterized coarse correlated equilibrium for a Vegas
correlated profile. -/
def IsCoarseCorrelatedEqFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (μ : CorrelatedProfile g) : Prop :=
  (behavioralKernelGame g).IsCoarseCorrelatedEqFor pref μ

end Vegas
