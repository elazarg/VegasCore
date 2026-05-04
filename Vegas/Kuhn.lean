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

/-- Finite Vegas mixed-to-behavioral realization in the IR-based behavioral
strategy space.

Every independent mixed profile over guard-legal pure strategies has a
machine-derived PMF behavioral realization with the same distribution over
payoff outcomes. A syntax-oriented client profile should be added only as a
separate presentation proved equivalent to this IR target. -/
theorem kuhn_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : LegalProgramBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  exact protocol_mixedPure_realizedByBehavioralPMF_finite
    g hctx LF μ

/-- Finite Vegas mixed-to-behavioral realization in the syntax-horizon
machine-derived FOSG strategy space. -/
theorem kuhn_mixedPure_realizedBySequentialBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  exact protocol_mixedPure_realizedBySequentialBehavioralPMF_finite
    g hctx LF μ

/-- Same theorem as `kuhn_mixedPure_realizedBySequentialBehavioralPMF_finite`,
with the carrier named explicitly.

The behavioral witness is a reachable legal profile of
`FOSGBridge.toFiniteGraphMachineFOSG g hctx`, and the preserved distribution
is the native Vegas pure strategic outcome kernel. -/
theorem kuhn_mixedPure_realizedByFiniteMachineFOSGBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  exact kuhn_mixedPure_realizedBySequentialBehavioralPMF_finite
    g hctx LF μ

/-- Finite Vegas mixed-to-behavioral realization in the reachable strategy
space of the observed adapter. This names the syntax-recursive projection
route, not the primary behavioral semantics. -/
theorem kuhn_mixedPure_realizedByReachableBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : ReachableProgramBehavioralProfilePMF g hctx,
      reachableProgramOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  exact protocol_mixedPure_realizedByReachableBehavioralPMF_finite
    g hctx LF μ

/-- The finite Vegas Kuhn property, packaged as a reusable proposition. -/
theorem kuhnPropertyPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    ProtocolTotalMixedPureRealizationPMF g hctx LF := by
  exact protocolTotalMixedPureRealizationPMF_finite g hctx LF

/-- The finite sequential Vegas Kuhn property, packaged as a reusable
proposition. -/
theorem sequentialKuhnPropertyPMF_finite
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
