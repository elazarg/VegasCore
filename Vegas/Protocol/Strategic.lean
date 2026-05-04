import Vegas.Protocol.EventLaw

/-!
# Machine-native strategic kernel games

This module gives the syntax-facing Vegas strategy spaces a machine-native
`KernelGame` presentation. The strategy carriers are the existing legal
strategy types, while outcome kernels run through the checked graph machine and
the event-law adapters from `Vegas.Protocol.EventLaw`.
-/

namespace Vegas

open GameTheory
open FOSGBridge

namespace GraphEventLaw

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Pure strategic form whose outcome kernel is the checked graph machine. -/
noncomputable def toMachineStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := LegalProgramPureStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (lawOfPure σ hctx).val (syntaxSteps g.prog)

@[simp] theorem toMachineStrategicKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (toMachineStrategicKernelGame g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (lawOfPure σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toMachineStrategicKernelGame_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toMachineStrategicKernelGame g hctx).Strategy =
      LegalProgramPureStrategy g := rfl

/-- PMF behavioral strategic form whose outcome kernel is the checked graph
machine. -/
noncomputable def toMachineKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := SyntaxLegalProgramBehavioralStrategyPMF g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (lawOfBehavioralPMF σ hctx).val (syntaxSteps g.prog)

@[simp] theorem toMachineKernelGamePMF_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : SyntaxLegalProgramBehavioralProfilePMF g) :
    (toMachineKernelGamePMF g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (lawOfBehavioralPMF σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toMachineKernelGamePMF_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toMachineKernelGamePMF g hctx).Strategy =
      SyntaxLegalProgramBehavioralStrategyPMF g := rfl

/-- FDist behavioral strategic form whose outcome kernel is the checked graph
machine. -/
noncomputable def toMachineKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := LegalProgramBehavioralStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (lawOfBehavioral σ hctx).val (syntaxSteps g.prog)

@[simp] theorem toMachineKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    (toMachineKernelGame g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (lawOfBehavioral σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem toMachineKernelGame_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toMachineKernelGame g hctx).Strategy =
      LegalProgramBehavioralStrategy g := rfl

end GraphEventLaw

export GraphEventLaw
  (toMachineStrategicKernelGame toMachineKernelGamePMF toMachineKernelGame)

end Vegas
