import Vegas.ProtocolSemantics

/-!
# Realization Theorems

Project-facing names for the finite mixed-to-PMF-behavioral realization
property of checked Vegas programs.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Finite checked Vegas programs satisfy mixed-to-PMF-behavioral realization
over the project kernel-game carriers. -/
theorem checkedProgram_kuhnPMF
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    KuhnPMF g :=
  kuhnPMF_finite g

/-- Independent mixed profiles over pure strategies have PMF behavioral
realizations with the same payoff-outcome distribution. -/
theorem checkedProgram_mixed_to_behavioral
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (μ : ∀ who, PMF ((pureKernelGameAt g).Strategy who)) :
    ∃ β : (pmfBehavioralKernelGameAt g).Profile,
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g).outcomeKernel π) :=
  kuhn_finite g μ

end Vegas
