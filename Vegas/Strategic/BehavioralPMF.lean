import Vegas.Strategic.Pure

/-!
# PMF Behavioral Strategic Semantics

This file defines the PMF behavioral strategic form for checked Vegas
programs.

The PMF strategy carrier is the reachable legal behavioral-strategy space at
the program's finite syntax horizon.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## PMF behavioral kernel game -/

/-- PMF-valued behavioral kernel game for a checked Vegas program.

The outcome kernel is `behavioralOutcomeKernelPMFAt`. -/
noncomputable def pmfBehavioralKernelGame [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : GameTheory.KernelGame P :=
  pmfBehavioralKernelGameAt g

@[simp] theorem pmfBehavioralKernelGame_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pmfBehavioralKernelGame g).Profile) :
    (pmfBehavioralKernelGame g).outcomeKernel σ =
      behavioralOutcomeKernelPMFAt g σ := rfl

@[simp] theorem pmfBehavioralKernelGame_udist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pmfBehavioralKernelGame g).Profile) :
    (pmfBehavioralKernelGame g).udist σ =
      (behavioralOutcomeKernelPMFAt g σ).bind
        (fun o : Outcome P => PMF.pure (fun i => (o i : ℝ))) := rfl

end Vegas
