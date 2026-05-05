import Vegas.PureStrategic

/-!
# PMF Behavioral Strategic Semantics

This file mirrors `Vegas.Strategic` and `Vegas.PureStrategic` but uses `PMF`
(Mathlib's probability mass functions) instead of `FDist` (rational Finsupp
distributions). The PMF layer is needed for theorem backends that produce
real-valued behavioral strategies.

The PMF strategy carrier is the reachable legal behavioral-strategy space of
the finite graph-machine FOSG at the program's syntax horizon.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## PMF behavioral kernel game -/

/-- PMF-valued behavioral kernel game for a checked Vegas program.

The outcome kernel is the finite graph-machine FOSG run distribution at the
bundle's context proof. -/
noncomputable def pmfBehavioralKernelGame [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] : GameTheory.KernelGame P :=
  pmfBehavioralKernelGameAt g g.wctx

@[simp] theorem pmfBehavioralKernelGame_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pmfBehavioralKernelGame g).Profile) :
    (pmfBehavioralKernelGame g).outcomeKernel σ =
      (pmfBehavioralKernelGameAt g g.wctx).outcomeKernel σ := rfl

@[simp] theorem pmfBehavioralKernelGame_udist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (σ : (pmfBehavioralKernelGame g).Profile) :
    (pmfBehavioralKernelGame g).udist σ =
      ((pmfBehavioralKernelGameAt g g.wctx).outcomeKernel σ).bind
        (fun o : Outcome P => PMF.pure (fun i => (o i : ℝ))) := rfl

end Vegas
