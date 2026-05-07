import Vegas.StrategicPMF
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties

/-!
# Vegas equilibrium wrappers

Game-theoretic vocabulary for finite Vegas programs, transported through the
PMF behavioral event-graph machine FOSG kernel game.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- PMF behavioral strategy profiles for a finite Vegas program. -/
def StrategyProfile [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : Type :=
  KernelGame.Profile (pmfBehavioralKernelGame g)

/-- A single player's PMF behavioral strategy in the finite FOSG game. -/
def Strategy [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] (who : P) : Type :=
  (pmfBehavioralKernelGame g).Strategy who

/-- Correlated profiles are profile distributions on the PMF behavioral
strategy-profile space. -/
def CorrelatedProfile [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : Type :=
  PMF (StrategyProfile g)

instance instFintypeGameStrategy [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Fintype (Strategy g who)] :
    ∀ who, Fintype ((pmfBehavioralKernelGame g).Strategy who) := by
  intro who
  let I : Fintype (Strategy g who) := inferInstance
  simpa [Strategy] using I

instance instNonemptyGameStrategy [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    [∀ who, Nonempty (Strategy g who)] :
    ∀ who, Nonempty ((pmfBehavioralKernelGame g).Strategy who) := by
  intro who
  let I : Nonempty (Strategy g who) := inferInstance
  simpa [Strategy] using I

instance instFintypeGameProfile [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    [Fintype (StrategyProfile g)] :
    Fintype (KernelGame.Profile (pmfBehavioralKernelGame g)) := by
  let I : Fintype (StrategyProfile g) := inferInstance
  simpa [StrategyProfile] using I

instance instNonemptyGameProfile [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    [Nonempty (StrategyProfile g)] :
    Nonempty (KernelGame.Profile (pmfBehavioralKernelGame g)) := by
  let I : Nonempty (StrategyProfile g) := inferInstance
  simpa [StrategyProfile] using I

/-- Expected utility for a Vegas PMF behavioral strategy profile. -/
noncomputable def eu [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g) (who : P) : ℝ :=
  (pmfBehavioralKernelGame g).eu σ who

/-- Correlated expected utility for a Vegas correlated profile. -/
noncomputable def correlatedEu [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (μ : CorrelatedProfile g) (who : P) : ℝ :=
  (pmfBehavioralKernelGame g).correlatedEu μ who

/-- EU weak preference on Vegas outcome distributions. -/
def euPref [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (pmfBehavioralKernelGame g).euPref

/-- EU strict preference on Vegas outcome distributions. -/
def euStrictPref [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (pmfBehavioralKernelGame g).euStrictPref

def IsNash [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsNash σ

def IsNashFor [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsNashFor pref σ

def IsBestResponse [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).IsBestResponse who σ s

def IsBestResponseFor [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).IsBestResponseFor pref who σ s

def IsDominant [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).IsDominant who s

def IsDominantFor [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).IsDominantFor pref who s

def IsStrictNash [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsStrictNash σ

def IsStrictDominant [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).IsStrictDominant who s

def ParetoDominates [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (σ τ : StrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).ParetoDominates σ τ

def IsParetoEfficient [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsParetoEfficient σ

noncomputable def socialWelfare [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (σ : StrategyProfile g) : ℝ :=
  (pmfBehavioralKernelGame g).socialWelfare σ

def IsCorrelatedEq [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (μ : CorrelatedProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsCorrelatedEq μ

def IsCoarseCorrelatedEq [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (μ : CorrelatedProfile g) : Prop :=
  (pmfBehavioralKernelGame g).IsCoarseCorrelatedEq μ

end Vegas
