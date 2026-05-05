import Vegas.StrategicPMF
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties

/-!
# Vegas equilibrium wrappers

Game-theoretic vocabulary for finite Vegas programs, transported through the
PMF behavioral graph-machine FOSG kernel game.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- PMF behavioral strategy profiles for a finite Vegas program. -/
def StrategyProfile [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) : Type :=
  KernelGame.Profile (pmfBehavioralKernelGame g LF)

/-- A single player's PMF behavioral strategy in the finite FOSG game. -/
def Strategy [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) (who : P) : Type :=
  (pmfBehavioralKernelGame g LF).Strategy who

/-- Correlated profiles are profile distributions on the PMF behavioral
strategy-profile space. -/
def CorrelatedProfile [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) : Type :=
  PMF (StrategyProfile g LF)

instance instFintypeGameStrategy [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    [∀ who, Fintype (Strategy g LF who)] :
    ∀ who, Fintype ((pmfBehavioralKernelGame g LF).Strategy who) := by
  intro who
  let I : Fintype (Strategy g LF who) := inferInstance
  simpa [Strategy] using I

instance instNonemptyGameStrategy [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    [∀ who, Nonempty (Strategy g LF who)] :
    ∀ who, Nonempty ((pmfBehavioralKernelGame g LF).Strategy who) := by
  intro who
  let I : Nonempty (Strategy g LF who) := inferInstance
  simpa [Strategy] using I

instance instFintypeGameProfile [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    [Fintype (StrategyProfile g LF)] :
    Fintype (KernelGame.Profile (pmfBehavioralKernelGame g LF)) := by
  let I : Fintype (StrategyProfile g LF) := inferInstance
  simpa [StrategyProfile] using I

instance instNonemptyGameProfile [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    [Nonempty (StrategyProfile g LF)] :
    Nonempty (KernelGame.Profile (pmfBehavioralKernelGame g LF)) := by
  let I : Nonempty (StrategyProfile g LF) := inferInstance
  simpa [StrategyProfile] using I

/-- Expected utility for a Vegas PMF behavioral strategy profile. -/
noncomputable def eu [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) (who : P) : ℝ :=
  (pmfBehavioralKernelGame g LF).eu σ who

/-- Correlated expected utility for a Vegas correlated profile. -/
noncomputable def correlatedEu [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (μ : CorrelatedProfile g LF) (who : P) : ℝ :=
  (pmfBehavioralKernelGame g LF).correlatedEu μ who

/-- EU weak preference on Vegas outcome distributions. -/
def euPref [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (pmfBehavioralKernelGame g LF).euPref

/-- EU strict preference on Vegas outcome distributions. -/
def euStrictPref [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (pmfBehavioralKernelGame g LF).euStrictPref

def IsNash [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsNash σ

def IsNashFor [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsNashFor pref σ

def IsBestResponse [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (σ : StrategyProfile g LF) (s : Strategy g LF who) : Prop :=
  (pmfBehavioralKernelGame g LF).IsBestResponse who σ s

def IsBestResponseFor [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (σ : StrategyProfile g LF) (s : Strategy g LF who) : Prop :=
  (pmfBehavioralKernelGame g LF).IsBestResponseFor pref who σ s

def IsDominant [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (s : Strategy g LF who) : Prop :=
  (pmfBehavioralKernelGame g LF).IsDominant who s

def IsDominantFor [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy g LF who) : Prop :=
  (pmfBehavioralKernelGame g LF).IsDominantFor pref who s

def IsStrictNash [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsStrictNash σ

def IsStrictDominant [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (s : Strategy g LF who) : Prop :=
  (pmfBehavioralKernelGame g LF).IsStrictDominant who s

def ParetoDominates [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (σ τ : StrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).ParetoDominates σ τ

def IsParetoEfficient [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsParetoEfficient σ

noncomputable def socialWelfare [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : StrategyProfile g LF) : ℝ :=
  (pmfBehavioralKernelGame g LF).socialWelfare σ

def IsCorrelatedEq [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (μ : CorrelatedProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsCorrelatedEq μ

def IsCoarseCorrelatedEq [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L)
    (μ : CorrelatedProfile g LF) : Prop :=
  (pmfBehavioralKernelGame g LF).IsCoarseCorrelatedEq μ

end Vegas
