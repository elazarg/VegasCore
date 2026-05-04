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

namespace GraphEventLaw

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Pure strategic form whose outcome kernel is the checked graph machine. -/
noncomputable def pureKernelGameAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := FeasibleProgramPureStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (pureEventLaw σ hctx).val (syntaxSteps g.prog)

@[simp] theorem pureKernelGameAt_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g) :
    (pureKernelGameAt g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (pureEventLaw σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem pureKernelGameAt_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (pureKernelGameAt g hctx).Strategy =
      FeasibleProgramPureStrategy g := rfl

/-- PMF behavioral strategic form whose outcome kernel is the checked graph
machine. -/
noncomputable def pmfBehavioralKernelGameAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := FeasibleProgramBehavioralStrategyPMF g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (pmfBehavioralEventLaw σ hctx).val (syntaxSteps g.prog)

@[simp] theorem pmfBehavioralKernelGameAt_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g) :
    (pmfBehavioralKernelGameAt g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (pmfBehavioralEventLaw σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem pmfBehavioralKernelGameAt_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (pmfBehavioralKernelGameAt g hctx).Strategy =
      FeasibleProgramBehavioralStrategyPMF g := rfl

/-- FDist behavioral strategic form whose outcome kernel is the checked graph
machine. -/
noncomputable def behavioralKernelGameAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P where
  Strategy := FeasibleProgramBehavioralStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (graphMachine g hctx).outcomeKernel
      (behavioralEventLaw σ hctx).val (syntaxSteps g.prog)

@[simp] theorem behavioralKernelGameAt_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfile g) :
    (behavioralKernelGameAt g hctx).outcomeKernel σ =
      (graphMachine g hctx).outcomeKernel
        (behavioralEventLaw σ hctx).val (syntaxSteps g.prog) := rfl

@[simp] theorem behavioralKernelGameAt_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (behavioralKernelGameAt g hctx).Strategy =
      FeasibleProgramBehavioralStrategy g := rfl

end GraphEventLaw

export GraphEventLaw
  (pureKernelGameAt pmfBehavioralKernelGameAt behavioralKernelGameAt)

end Vegas
