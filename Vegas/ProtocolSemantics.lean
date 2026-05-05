import Vegas.Kuhn

/-!
# Protocol-level semantic properties

This module keeps the protocol-facing named realization property after the
strategic semantics collapse. The canonical statement is the finite
graph-machine FOSG kernel theorem: mixed profiles over `pureKernelGameAt`
strategies are realized by PMF behavioral profiles of
`pmfBehavioralKernelGameAt` with the same outcome distribution.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Finite protocol-level Kuhn property for the graph-machine FOSG kernel
games. -/
def KuhnPMF [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) : Prop :=
  ∀ (μ : ∀ who, PMF ((pureKernelGameAt g hctx LF).Strategy who)),
    letI : Fintype (graphMachine g hctx).State :=
      graphMachine.instFintypeState g hctx LF
    letI : ∀ who : P,
        Fintype (Option ((graphMachine g hctx).Action who)) :=
      fun who => graphMachine.instFintypeOptionAction g hctx LF who
    letI : Fintype (graphMachine g hctx).Event :=
      graphMachine.instFintypeEvent g hctx LF
    letI : Fintype
        ((graphMachine g hctx).BoundedRunPrefix (syntaxSteps g.prog)) :=
      Machine.BoundedRunPrefix.instFintype
    letI : Fintype
        (((fosgView g hctx).toBoundedFOSG
            (syntaxSteps g.prog)).History) :=
      boundedFOSG.instFintypeHistory g hctx (syntaxSteps g.prog)
    letI : DecidablePred
        (((fosgView g hctx).toBoundedFOSG
            (syntaxSteps g.prog)).terminal) :=
      Classical.decPred _
    letI : ∀ who : P,
        Fintype ((pureKernelGameAt g hctx LF).Strategy who) := by
      intro who
      dsimp [pureKernelGameAt, pureStrategyAt,
        Machine.FOSGView.BoundedPureStrategy]
      infer_instance
    ∃ β : (pmfBehavioralKernelGameAt g hctx LF).Profile,
      (pmfBehavioralKernelGameAt g hctx LF).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g hctx LF).outcomeKernel π)

/-- The finite graph-machine FOSG kernel games satisfy Kuhn's mixed-to-PMF
behavioral realization property. -/
theorem kuhnPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    KuhnPMF g hctx LF := by
  intro μ
  exact kuhn_finite g hctx LF μ

end Vegas
