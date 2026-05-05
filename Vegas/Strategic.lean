import GameTheory.Core.KernelGame
import Vegas.Protocol.Strategic
import Vegas.Strategy.Behavioral

/-!
# Strategic semantics bridge

The fixed-program behavioral carrier lives in `Vegas.Strategy.Behavioral`;
the public `behavioralKernelGame` constructor is machine-backed.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Vegas denotational semantics as a `KernelGame` whose strategies are the
fixed program's local *guard-legal* behavioral strategies.

This is the public behavioral strategic form. Its outcome kernel is the
checked graph-machine kernel at the program bundle's context proof. -/
noncomputable def behavioralKernelGame (g : WFProgram P L) : GameTheory.KernelGame P :=
  syntaxBehavioralKernelGameAt g g.wctx

@[simp] theorem behavioralKernelGame_outcomeKernel
    (g : WFProgram P L)
    (σ : FeasibleProgramBehavioralProfile g) :
    (behavioralKernelGame g).outcomeKernel σ =
      (graphMachine g g.wctx).outcomeKernel
        (behavioralEventLaw σ g.wctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem behavioralKernelGame_udist
    (g : WFProgram P L)
    (σ : FeasibleProgramBehavioralProfile g) :
    (behavioralKernelGame g).udist σ =
      ((graphMachine g g.wctx).outcomeKernel
        (behavioralEventLaw σ g.wctx).val (syntaxSteps g.prog)).bind
        (fun o : Outcome P => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- `behavioralKernelGame` is the machine-native behavioral kernel at `g.wctx`. -/
theorem behavioralKernelGame_eu
    (g : WFProgram P L)
    (σ : FeasibleProgramBehavioralProfile g) (who : P) :
    (behavioralKernelGame g).eu σ who =
      (syntaxBehavioralKernelGameAt g g.wctx).eu σ who := rfl

end Vegas
