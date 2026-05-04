import Vegas.PureStrategic
import Vegas.Strategic
import Vegas.Strategy.Conversions

/-!
# PMF Behavioral Strategic Semantics

This file mirrors `Vegas.Strategic` and `Vegas.PureStrategic` but uses `PMF`
(Mathlib's probability mass functions) instead of `FDist` (rational Finsupp
distributions). The PMF layer is needed for theorem backends that produce
real-valued behavioral strategies.

The PMF strategy carrier lives in `Vegas.Strategy.PMF`; the syntax-recursive
carrier conversions live in `Vegas.Strategy.Conversions`. The public PMF
behavioral `KernelGame` presentation is machine-backed.
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
noncomputable def pmfBehavioralKernelGame (g : WFProgram P L) : GameTheory.KernelGame P :=
  pmfBehavioralKernelGameAt g g.wctx

@[simp] theorem pmfBehavioralKernelGame_outcomeKernel
    (g : WFProgram P L) (σ : FeasibleProgramBehavioralProfilePMF g) :
    (pmfBehavioralKernelGame g).outcomeKernel σ =
      (graphMachine g g.wctx).outcomeKernel
        (pmfBehavioralEventLaw σ g.wctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem pmfBehavioralKernelGame_udist
    (g : WFProgram P L) (σ : FeasibleProgramBehavioralProfilePMF g) :
    (pmfBehavioralKernelGame g).udist σ =
      ((graphMachine g g.wctx).outcomeKernel
        (pmfBehavioralEventLaw σ g.wctx).val (syntaxSteps g.prog)).bind
        (fun o : Outcome P => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- The PMF conversion of an FDist behavioral profile has the same outcome
kernel as the original FDist-valued kernel game profile. -/
theorem pmfBehavioralKernelGame_outcomeKernel_toPMFProfile_eq_behavioralKernelGame
    (g : WFProgram P L)
    (σ : FeasibleProgramBehavioralProfile g) :
    (pmfBehavioralKernelGame g).outcomeKernel
        (FeasibleProgramBehavioralProfile.toPMFProfile σ) =
      (behavioralKernelGame g).outcomeKernel σ := by
  rfl

/-- The PMF behavioral lift of a legal pure profile has the same outcome
kernel as the fixed-program pure strategic form. -/
theorem pmfBehavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioralPMF
    (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) :
    (pmfBehavioralKernelGame g).outcomeKernel
        (FeasibleProgramPureProfile.toBehavioralPMF σ) =
      (pureKernelGame g).outcomeKernel σ := by
  rfl

end Vegas
