import Vegas.PureStrategic
import Vegas.Strategic

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

Unlike `behavioralKernelGame`, this game uses `PMF` behavioral strategies directly.
That matters for Kuhn mixed-to-behavioral results: an arbitrary mixed strategy
over pure profiles can induce real-valued behavioral probabilities, which need
not be representable by Vegas' rational `FDist` kernels.

The outcome kernel is the checked graph-machine kernel at the bundle's context
proof. -/
noncomputable def pmfBehavioralKernelGame [Fintype P]
    (g : WFProgram P L) (LF : FiniteValuation L) : GameTheory.KernelGame P :=
  pmfBehavioralKernelGameAt g g.wctx LF

@[simp] theorem pmfBehavioralKernelGame_outcomeKernel
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : (pmfBehavioralKernelGame g LF).Profile) :
    (pmfBehavioralKernelGame g LF).outcomeKernel σ =
      (pmfBehavioralKernelGameAt g g.wctx LF).outcomeKernel σ := rfl

@[simp] theorem pmfBehavioralKernelGame_udist
    [Fintype P] (g : WFProgram P L) (LF : FiniteValuation L)
    (σ : (pmfBehavioralKernelGame g LF).Profile) :
    (pmfBehavioralKernelGame g LF).udist σ =
      ((pmfBehavioralKernelGameAt g g.wctx LF).outcomeKernel σ).bind
        (fun o : Outcome P => PMF.pure (fun i => (o i : ℝ))) := rfl

end Vegas
