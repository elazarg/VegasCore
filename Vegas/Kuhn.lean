import Vegas.Protocol.Kuhn

/-!
# Kuhn realization for Vegas

This file exposes the Vegas-facing mixed-to-behavioral realization theorem.
The statement preserves outcome distributions; expected-utility equalities are
ordinary corollaries of this distribution equality.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Finite Vegas mixed-to-behavioral realization.

Every independent mixed profile over reachable legal pure strategies of the
finite Vegas pure kernel game has a PMF behavioral realization with the same
distribution over payoff outcomes. -/
theorem kuhn_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF ((pureKernelGameAt g hctx LF).Strategy who)) :
    ∃ β : (pmfBehavioralKernelGameAt g hctx LF).Profile,
      (pmfBehavioralKernelGameAt g hctx LF).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g hctx LF).outcomeKernel π) := by
  exact kuhn_finiteKernelGame g hctx LF μ

end Vegas
