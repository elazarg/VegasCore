import Vegas.GameBridge.FOSG.Kuhn

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
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (bridge : NativeFOSGKuhnBridge g)
    (μ : ∀ who, PMF ((pureKernelGameAt g).Strategy who)) :
    ∃ β : (pmfBehavioralKernelGameAt g).Profile,
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g).outcomeKernel π) := by
  exact kuhn_finiteKernelGame_of_nativeFOSGBridge g bridge μ

end Vegas
