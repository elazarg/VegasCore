import GameTheory.Core.KernelGame
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties
import Vegas.Finite
import Vegas.Strategic
import Vegas.Strategy.Conversions
import Vegas.Strategy.Pure

/-!
# Fixed-Program Pure Strategic Form

This file defines the pure strategic form for a fixed Vegas program.

Unlike a global policy space over all contexts and guards, `ProgramPureStrategy
who p` contains one deterministic choice rule for each commit site of the fixed
program `p` owned by `who`. The carrier itself lives in `Vegas.Strategy.Pure`.
The public pure `KernelGame` constructor is machine-backed.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Fixed-program pure strategic form of a Vegas program.

The outcome kernel is the checked graph-machine kernel at the bundle's context
proof. -/
noncomputable def pureKernelGame (g : WFProgram P L) :
    GameTheory.KernelGame P :=
  pureKernelGameAt g g.wctx

@[simp] theorem pureKernelGame_outcomeKernel
    (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) :
    (pureKernelGame g).outcomeKernel σ =
      (graphMachine g g.wctx).outcomeKernel
        (pureEventLaw σ g.wctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem pureKernelGame_Strategy (g : WFProgram P L) :
    (pureKernelGame g).Strategy = FeasibleProgramPureStrategy g := rfl

/-- `pureKernelGame` is the machine-native pure kernel at `g.wctx`. -/
theorem pureKernelGame_eu
    (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) (who : P) :
    (pureKernelGame g).eu σ who =
      (pureKernelGameAt g g.wctx).eu σ who := rfl

/-- The legal behavioral lift of a legal pure profile has the same outcome
kernel as the fixed-program pure strategic form. -/
theorem behavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioral
    (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) :
    (behavioralKernelGame g).outcomeKernel
        (FeasibleProgramPureProfile.toBehavioral σ) =
      (pureKernelGame g).outcomeKernel σ := by
  change (graphMachine g g.wctx).outcomeKernel
        (pmfBehavioralEventLaw
          (FeasibleProgramBehavioralProfile.toPMFProfile
            (FeasibleProgramPureProfile.toBehavioral σ)) g.wctx).val
        (syntaxSteps g.prog) =
      (graphMachine g g.wctx).outcomeKernel
        (pmfBehavioralEventLaw
          (FeasibleProgramPureProfile.toBehavioralPMF σ) g.wctx).val
        (syntaxSteps g.prog)
  congr 2
  ext cfg
  rw [show
      FeasibleProgramBehavioralProfile.toPMFProfile
          (FeasibleProgramPureProfile.toBehavioral σ) =
        FeasibleProgramPureProfile.toBehavioralPMF σ by
      funext who
      apply Subtype.ext
      simpa [FeasibleProgramBehavioralProfile.toPMFProfile,
        FeasibleProgramPureProfile.toBehavioral,
        FeasibleProgramPureProfile.toBehavioralPMF] using
        congrFun
          (ProgramBehavioralProfile.toPMFProfile_toBehavioral_eq_toBehavioralPMF
            g.prog (fun i => (σ i).val)) who]

/-- The legal behavioral lift of a legal pure profile has the same expected
utility as the fixed-program pure strategic form. -/
theorem behavioralKernelGame_eu_eq_pureKernelGame_toBehavioral
    (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) (who : P) :
    (behavioralKernelGame g).eu
        (FeasibleProgramPureProfile.toBehavioral σ) who =
      (pureKernelGame g).eu σ who := by
  unfold GameTheory.KernelGame.eu
  rw [behavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioral]
  rfl

/-- Pure Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureNash (g : WFProgram P L) (σ : FeasibleProgramPureProfile g) : Prop :=
  (pureKernelGame g).IsNash σ

/-- Pure dominant strategy in the fixed-program Vegas strategic form. -/
def IsPureDominant (g : WFProgram P L)
    (who : P) (s : FeasibleProgramPureStrategy g who) : Prop :=
  (pureKernelGame g).IsDominant who s

/-- Pure best response in the fixed-program Vegas strategic form. -/
def IsPureBestResponse (g : WFProgram P L)
    (who : P) (σ : FeasibleProgramPureProfile g)
    (s : FeasibleProgramPureStrategy g who) : Prop :=
  (pureKernelGame g).IsBestResponse who σ s

/-- Pure strict Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureStrictNash (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) : Prop :=
  (pureKernelGame g).IsStrictNash σ

/-- Exact potential for the fixed-program Vegas strategic form. -/
def IsPureExactPotential (g : WFProgram P L)
    (Φ : FeasibleProgramPureProfile g → ℝ) : Prop :=
  (pureKernelGame g).IsExactPotential Φ

/-- Ordinal potential for the fixed-program Vegas strategic form. -/
def IsPureOrdinalPotential (g : WFProgram P L)
    (Φ : FeasibleProgramPureProfile g → ℝ) : Prop :=
  (pureKernelGame g).IsOrdinalPotential Φ

end Vegas
