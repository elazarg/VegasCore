import Vegas.Strategic.Kuhn

/-!
# Protocol-level semantic properties

This module keeps the protocol-facing named realization property after the
strategic semantics collapse. The canonical statement is the finite Vegas
kernel-game theorem: mixed profiles over `pureKernelGameAt` strategies are
realized by PMF behavioral profiles of `pmfBehavioralKernelGameAt` with the
same outcome distribution.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Finite protocol-level Kuhn property for the event-graph machine FOSG kernel
games. -/
def KuhnPMF [Fintype P] (g : WFProgram P L)
    [FiniteDomains g] : Prop :=
  ∀ (μ : ∀ who, PMF ((pureKernelGameAt g).Strategy who)),
    ∃ β : (pmfBehavioralKernelGameAt g).Profile,
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g).outcomeKernel π)

/-- The finite Vegas kernel games satisfy Kuhn's mixed-to-PMF
behavioral realization property. -/
theorem kuhnPMF_finite
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    KuhnPMF g := by
  intro μ
  exact kuhn_finite g μ

end Vegas
