import GameTheory.Core.KernelGame
import Vegas.Protocol.Strategic
import Vegas.Strategy.Behavioral

/-!
# Strategic semantics bridge

The fixed-program behavioral carrier lives in `Vegas.Strategy.Behavioral`;
the public `toKernelGame` constructor is machine-backed.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Vegas denotational semantics as a `KernelGame` whose strategies are the
fixed program's local *guard-legal* behavioral strategies.

This is the public behavioral strategic form. Its outcome kernel is the
checked graph-machine kernel at the program bundle's context proof. -/
noncomputable def toKernelGame (g : WFProgram P L) : GameTheory.KernelGame P :=
  toMachineKernelGame g g.wctx

@[simp] theorem toKernelGame_outcomeKernel
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGame g).outcomeKernel σ =
      (graphMachine g g.wctx).outcomeKernel
        (lawOfBehavioral σ g.wctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toKernelGame_udist
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGame g).udist σ =
      ((graphMachine g g.wctx).outcomeKernel
        (lawOfBehavioral σ g.wctx).val (syntaxSteps g.prog)).bind
        (fun o : Outcome P => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- `toKernelGame` is the machine-native behavioral kernel at `g.wctx`. -/
theorem toKernelGame_eu
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    (toKernelGame g).eu σ who =
      (toMachineKernelGame g g.wctx).eu σ who := rfl

end Vegas
