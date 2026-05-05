import Vegas.Protocol.Strategic
import Vegas.StrategicPMF

/-!
# Compatibility for machine-native strategic kernels

The primary strategic kernel definitions live in `Vegas.Protocol.Strategic`.
This module contains the temporary comparison theorems between arbitrary
context proofs `hctx`, the public `g.wctx` strategic constructors, and the
remaining syntax-recursive evaluator lemmas. Keeping these lemmas here prevents
the low-level event-law and machine-strategic modules from importing legacy
strategic compatibility material.
-/

namespace Vegas

open GameTheory

namespace GraphEventLaw

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {g : WFProgram P L}

/-- PMF behavioral profiles have the same outcome kernel through any checked
context proof as through the public PMF kernel at `g.wctx`. -/
theorem pmfBehavioralEventLaw_outcomeKernel_eq_pmfBehavioralKernelGame
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).outcomeKernel
        (pmfBehavioralEventLaw σ hctx).val (syntaxSteps g.prog) =
      (pmfBehavioralKernelGame g).outcomeKernel σ := by
  rw [pmfBehavioralEventLaw_outcomeKernel_eq_cursorVegasOutcomeKernelPMF]
  rw [show
      (pmfBehavioralKernelGame g).outcomeKernel σ =
        (graphMachine g g.wctx).outcomeKernel
          (pmfBehavioralEventLaw σ g.wctx).val (syntaxSteps g.prog) by
        rfl]
  rw [pmfBehavioralEventLaw_outcomeKernel_eq_cursorVegasOutcomeKernelPMF
    (g := g) (σ := σ) (hctx := g.wctx)]

/-- FDist-valued legal behavioral profiles have the same outcome kernel
through any checked context proof as through the public behavioral kernel. -/
theorem behavioralEventLaw_outcomeKernel_eq_behavioralKernelGame
    (σ : FeasibleProgramBehavioralProfile g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).outcomeKernel
        (behavioralEventLaw σ hctx).val (syntaxSteps g.prog) =
      (behavioralKernelGame g).outcomeKernel σ := by
  rw [behavioralEventLaw]
  rw [pmfBehavioralEventLaw_outcomeKernel_eq_pmfBehavioralKernelGame]
  exact pmfBehavioralKernelGame_outcomeKernel_toPMFProfile_eq_behavioralKernelGame g σ

/-- Pure profiles have the same outcome kernel through any checked context
proof as through the public pure strategic kernel. -/
theorem pureEventLaw_outcomeKernel_eq_pureKernelGame
    (σ : FeasibleProgramPureProfile g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).outcomeKernel
        (pureEventLaw σ hctx).val (syntaxSteps g.prog) =
      (pureKernelGame g).outcomeKernel σ := by
  rw [pureEventLaw]
  rw [pmfBehavioralEventLaw_outcomeKernel_eq_pmfBehavioralKernelGame]
  exact pmfBehavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioralPMF
    g σ

/-- The `hctx`-indexed machine pure kernel agrees with the public pure kernel. -/
theorem pureKernelGameAt_outcomeKernel_eq_pureKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g) :
    (syntaxPureKernelGameAt g hctx).outcomeKernel σ =
      (pureKernelGame g).outcomeKernel σ :=
  pureEventLaw_outcomeKernel_eq_pureKernelGame σ hctx

/-- Expected utilities are unchanged by changing the pure kernel's context
proof. -/
theorem pureKernelGameAt_eu_eq_pureKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g) (who : P) :
    (syntaxPureKernelGameAt g hctx).eu σ who =
      (pureKernelGame g).eu σ who := by
  unfold GameTheory.KernelGame.eu
  rw [pureKernelGameAt_outcomeKernel_eq_pureKernelGame]
  simp [syntaxPureKernelGameAt, pureKernelGame]

/-- Utility distributions are unchanged by changing the pure kernel's context
proof. -/
theorem pureKernelGameAt_udist_eq_pureKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g) :
    (syntaxPureKernelGameAt g hctx).udist σ =
      (pureKernelGame g).udist σ := by
  unfold GameTheory.KernelGame.udist
  rw [pureKernelGameAt_outcomeKernel_eq_pureKernelGame]
  simp [syntaxPureKernelGameAt, pureKernelGame]

/-- Binding a distribution over pure profiles is unchanged by changing the
pure kernel's context proof. -/
theorem bind_pureKernelGameAt_outcomeKernel_eq_pureKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : PMF (FeasibleProgramPureProfile g)) :
    μ.bind (fun σ => (syntaxPureKernelGameAt g hctx).outcomeKernel σ) =
      μ.bind (fun σ => (pureKernelGame g).outcomeKernel σ) := by
  refine Math.ProbabilityMassFunction.bind_congr_on_support μ _ _ ?_
  intro σ _
  exact pureKernelGameAt_outcomeKernel_eq_pureKernelGame
    g hctx σ

/-- The `hctx`-indexed machine PMF behavioral kernel agrees with the public PMF
behavioral kernel. -/
theorem pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g) :
    (syntaxPMFBehavioralKernelGameAt g hctx).outcomeKernel σ =
      (pmfBehavioralKernelGame g).outcomeKernel σ :=
  pmfBehavioralEventLaw_outcomeKernel_eq_pmfBehavioralKernelGame σ hctx

/-- Expected utilities are unchanged by changing the PMF behavioral kernel's
context proof. -/
theorem pmfBehavioralKernelGameAt_eu_eq_pmfBehavioralKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g) (who : P) :
    (syntaxPMFBehavioralKernelGameAt g hctx).eu σ who =
      (pmfBehavioralKernelGame g).eu σ who := by
  unfold GameTheory.KernelGame.eu
  rw [pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame]
  simp [syntaxPMFBehavioralKernelGameAt, pmfBehavioralKernelGame]

/-- Utility distributions are unchanged by changing the PMF behavioral kernel's
context proof. -/
theorem pmfBehavioralKernelGameAt_udist_eq_pmfBehavioralKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g) :
    (syntaxPMFBehavioralKernelGameAt g hctx).udist σ =
      (pmfBehavioralKernelGame g).udist σ := by
  unfold GameTheory.KernelGame.udist
  rw [pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame]
  simp [syntaxPMFBehavioralKernelGameAt, pmfBehavioralKernelGame]

/-- Binding a distribution over PMF behavioral profiles is unchanged by
changing the PMF behavioral kernel's context proof. -/
theorem bind_pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : PMF (FeasibleProgramBehavioralProfilePMF g)) :
    μ.bind (fun σ =>
        (syntaxPMFBehavioralKernelGameAt g hctx).outcomeKernel σ) =
      μ.bind (fun σ => (pmfBehavioralKernelGame g).outcomeKernel σ) := by
  refine Math.ProbabilityMassFunction.bind_congr_on_support μ _ _ ?_
  intro σ _
  exact pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame g hctx σ

/-- The `hctx`-indexed machine FDist behavioral kernel agrees with the public
FDist behavioral kernel. -/
theorem behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfile g) :
    (syntaxBehavioralKernelGameAt g hctx).outcomeKernel σ =
      (behavioralKernelGame g).outcomeKernel σ :=
  behavioralEventLaw_outcomeKernel_eq_behavioralKernelGame σ hctx

/-- Expected utilities are unchanged by changing the FDist behavioral kernel's
context proof. -/
theorem behavioralKernelGameAt_eu_eq_behavioralKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfile g) (who : P) :
    (syntaxBehavioralKernelGameAt g hctx).eu σ who =
      (behavioralKernelGame g).eu σ who := by
  unfold GameTheory.KernelGame.eu
  rw [behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame]
  simp [syntaxBehavioralKernelGameAt, behavioralKernelGame]

/-- Utility distributions are unchanged by changing the FDist behavioral
kernel's context proof. -/
theorem behavioralKernelGameAt_udist_eq_behavioralKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfile g) :
    (syntaxBehavioralKernelGameAt g hctx).udist σ =
      (behavioralKernelGame g).udist σ := by
  unfold GameTheory.KernelGame.udist
  rw [behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame]
  simp [syntaxBehavioralKernelGameAt, behavioralKernelGame]

/-- Binding a distribution over FDist behavioral profiles is unchanged by
changing the FDist behavioral kernel's context proof. -/
theorem bind_behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : PMF (FeasibleProgramBehavioralProfile g)) :
    μ.bind (fun σ => (syntaxBehavioralKernelGameAt g hctx).outcomeKernel σ) =
      μ.bind (fun σ => (behavioralKernelGame g).outcomeKernel σ) := by
  refine Math.ProbabilityMassFunction.bind_congr_on_support μ _ _ ?_
  intro σ _
  exact behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame g hctx σ

end GraphEventLaw

export GraphEventLaw
  (pmfBehavioralEventLaw_outcomeKernel_eq_pmfBehavioralKernelGame
   behavioralEventLaw_outcomeKernel_eq_behavioralKernelGame
   pureEventLaw_outcomeKernel_eq_pureKernelGame
   pureKernelGameAt_outcomeKernel_eq_pureKernelGame
   pureKernelGameAt_eu_eq_pureKernelGame
   pureKernelGameAt_udist_eq_pureKernelGame
   bind_pureKernelGameAt_outcomeKernel_eq_pureKernelGame
   pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame
   pmfBehavioralKernelGameAt_eu_eq_pmfBehavioralKernelGame
   pmfBehavioralKernelGameAt_udist_eq_pmfBehavioralKernelGame
   bind_pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame
   behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame
   behavioralKernelGameAt_eu_eq_behavioralKernelGame
   behavioralKernelGameAt_udist_eq_behavioralKernelGame
   bind_behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame)

end Vegas
