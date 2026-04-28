import Vegas.FOSG.Observed.Kernel

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-!
# FOSG denotation for checked Vegas programs

This file is the public entrypoint for the FOSG integration. The internal
`Observed` modules contain the cursor machinery and proof infrastructure; the
definitions below expose the intended denotational surface.
-/

/-- Canonical sequential denotation of a checked Vegas program as a FOSG. -/
noncomputable abbrev toFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  observedProgramFOSG g hctx

theorem toFOSG_legalObservable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toFOSG g hctx).LegalObservable :=
  Observed.observedProgramFOSG_legalObservable g hctx

theorem toFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toFOSG g hctx).BoundedHorizon (syntaxSteps g.prog) :=
  observedProgramFOSG_boundedHorizon g hctx

/-- Strategic KernelGame view of the canonical FOSG denotation. -/
noncomputable abbrev toFOSGKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] : KernelGame P :=
  Observed.observedProgramReachableKernelGame g hctx LF

@[simp] theorem toFOSGKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (toFOSG g hctx).ReachableLegalBehavioralProfile) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : DecidablePred (toFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    (toFOSGKernelGame g hctx LF).outcomeKernel β =
      PMF.map (observedProgramHistoryOutcome g hctx)
        ((toFOSG g hctx).runDist (syntaxSteps g.prog) β.extend) := by
  exact Observed.observedProgramReachableKernelGame_outcomeKernel
    g hctx LF β

/-- FOSG Kuhn M→B, specialized to product-mixed Vegas pure strategies and
stated as preservation of the Vegas outcome distribution. -/
theorem toFOSG_mixedPure_realizedByBehavioral_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : KernelGame.Profile (toFOSGKernelGame g hctx LF),
      (toFOSGKernelGame g hctx LF).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) :=
  Observed.observedProgramReachableKernelGame_mixedPure_realization
    g hctx LF μ

end FOSGBridge
end Vegas
