import Vegas.ProtocolSemantics

/-!
# Kuhn realization for Vegas

This file exposes the Vegas-facing mixed-to-behavioral realization theorem.
The statement preserves outcome distributions; expected-utility equalities are
ordinary corollaries of this distribution equality.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Finite Vegas mixed-to-behavioral realization in the reachable strategy
space.

Every independent mixed profile over guard-legal pure strategies has a
reachable PMF behavioral realization with the same distribution over payoff
outcomes. The behavioral witness is intentionally reachable-indexed: it assigns
behavior only to observations that can arise during the sequential execution. -/
theorem kuhn_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : ReachableProgramBehavioralProfilePMF g hctx,
      reachableProgramOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  exact protocol_mixedPure_realizedByReachableBehavioralPMF_finite
    g hctx LF μ

/-- The finite Vegas Kuhn property, packaged as a reusable proposition. -/
theorem kuhnPropertyPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    ProtocolReachableKuhnPropertyPMF g hctx LF := by
  exact protocolReachableKuhnPropertyPMF_finite g hctx LF

end Vegas
