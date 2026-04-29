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

/-- Finite Vegas mixed-to-behavioral realization in the sequential strategy
space.

Every independent mixed profile over guard-legal pure strategies has a total
PMF behavioral realization for the sequential denotation with the same
distribution over payoff outcomes. -/
theorem kuhn_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  exact protocol_mixedPure_realizedByBehavioralPMF_finite
    g hctx LF μ

/-- Finite Vegas mixed-to-behavioral realization in the reachable strategy
space. This is useful when only reachable observations should be assigned
behavior. -/
theorem kuhn_mixedPure_realizedByReachableBehavioralPMF_finite
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

/-- The finite sequential Vegas Kuhn property, packaged as a reusable
proposition. -/
theorem kuhnPropertyPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    ProtocolSequentialKuhnPropertyPMF g hctx LF := by
  exact protocolSequentialKuhnPropertyPMF_finite g hctx LF

/-- The finite reachable Vegas Kuhn property, packaged as a reusable
proposition. -/
theorem reachableKuhnPropertyPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    ProtocolReachableKuhnPropertyPMF g hctx LF := by
  exact protocolReachableKuhnPropertyPMF_finite g hctx LF

end Vegas
