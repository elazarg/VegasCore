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

/-! ## Finite FOSG-native kernel games

These constructors are the replacement semantic surface. Their strategy spaces
are reachable legal strategies of the bounded graph-machine FOSG, and their
outcome kernels are the bounded FOSG run distributions marginalized to Vegas
outcomes. The old event-law constructors above stay temporarily while
downstream files are flipped one at a time.
-/

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Pure strategy carrier of the finite graph-machine FOSG at the program's
syntax horizon. -/
abbrev finitePureStrategyAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) : Type :=
  (fosgView g hctx).BoundedPureStrategy (syntaxSteps g.prog) who

/-- Pure profile carrier of the finite graph-machine FOSG. -/
abbrev finitePureProfileAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Type :=
  (fosgView g hctx).BoundedPureProfile (syntaxSteps g.prog)

/-- PMF behavioral strategy carrier of the finite graph-machine FOSG at the
program's syntax horizon. -/
abbrev finiteBehavioralStrategyPMFAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) : Type :=
  (fosgView g hctx).BoundedBehavioralStrategy (syntaxSteps g.prog) who

/-- PMF behavioral profile carrier of the finite graph-machine FOSG. -/
abbrev finiteBehavioralProfilePMFAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Type :=
  (fosgView g hctx).BoundedBehavioralProfile (syntaxSteps g.prog)

/-- Finite FOSG-native pure strategic form of a checked Vegas program. -/
noncomputable def finitePureKernelGameAt
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) : GameTheory.KernelGame P where
  Strategy := finitePureStrategyAt g hctx
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun π => by
    classical
    letI : Fintype (graphMachine g hctx).State :=
      graphMachine.instFintypeState g hctx LF
    letI : ∀ who : P,
        Fintype (Option ((graphMachine g hctx).Action who)) :=
      fun who => graphMachine.instFintypeOptionAction g hctx LF who
    letI : Fintype (graphMachine g hctx).Event :=
      graphMachine.instFintypeEvent g hctx LF
    letI :
        Fintype
          ((graphMachine g hctx).BoundedRunPrefix
            (syntaxSteps g.prog)) :=
      Machine.BoundedRunPrefix.instFintype
    letI : DecidablePred
        (((fosgView g hctx).toBoundedFOSG
          (syntaxSteps g.prog)).terminal) :=
      Classical.decPred _
    exact
      (fosgView g hctx).boundedOutcomeFromPure
        (syntaxSteps g.prog) π (syntaxSteps g.prog)

@[simp] theorem finitePureKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) :
    (finitePureKernelGameAt g hctx LF).Strategy =
      finitePureStrategyAt g hctx := rfl

@[simp] theorem finitePureKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) (π : finitePureProfileAt g hctx) :
    (finitePureKernelGameAt g hctx LF).outcomeKernel π =
      (by
        classical
        letI : Fintype (graphMachine g hctx).State :=
          graphMachine.instFintypeState g hctx LF
        letI : ∀ who : P,
            Fintype (Option ((graphMachine g hctx).Action who)) :=
          fun who => graphMachine.instFintypeOptionAction g hctx LF who
        letI : Fintype (graphMachine g hctx).Event :=
          graphMachine.instFintypeEvent g hctx LF
        letI :
            Fintype
              ((graphMachine g hctx).BoundedRunPrefix
                (syntaxSteps g.prog)) :=
          Machine.BoundedRunPrefix.instFintype
        letI : DecidablePred
            (((fosgView g hctx).toBoundedFOSG
              (syntaxSteps g.prog)).terminal) :=
          Classical.decPred _
        exact
          (fosgView g hctx).boundedOutcomeFromPure
            (syntaxSteps g.prog) π (syntaxSteps g.prog)) := rfl

/-- Finite FOSG-native PMF behavioral strategic form of a checked Vegas
program. -/
noncomputable def finiteBehavioralKernelGamePMFAt
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) : GameTheory.KernelGame P where
  Strategy := finiteBehavioralStrategyPMFAt g hctx
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun β => by
    classical
    letI : Fintype (graphMachine g hctx).State :=
      graphMachine.instFintypeState g hctx LF
    letI : ∀ who : P,
        Fintype (Option ((graphMachine g hctx).Action who)) :=
      fun who => graphMachine.instFintypeOptionAction g hctx LF who
    letI : Fintype (graphMachine g hctx).Event :=
      graphMachine.instFintypeEvent g hctx LF
    letI :
        Fintype
          ((graphMachine g hctx).BoundedRunPrefix
            (syntaxSteps g.prog)) :=
      Machine.BoundedRunPrefix.instFintype
    letI : DecidablePred
        (((fosgView g hctx).toBoundedFOSG
          (syntaxSteps g.prog)).terminal) :=
      Classical.decPred _
    exact
      (fosgView g hctx).boundedOutcomeFromBehavioral
        (syntaxSteps g.prog) β (syntaxSteps g.prog)

@[simp] theorem finiteBehavioralKernelGamePMFAt_Strategy
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) :
    (finiteBehavioralKernelGamePMFAt g hctx LF).Strategy =
      finiteBehavioralStrategyPMFAt g hctx := rfl

@[simp] theorem finiteBehavioralKernelGamePMFAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) (β : finiteBehavioralProfilePMFAt g hctx) :
    (finiteBehavioralKernelGamePMFAt g hctx LF).outcomeKernel β =
      (by
        classical
        letI : Fintype (graphMachine g hctx).State :=
          graphMachine.instFintypeState g hctx LF
        letI : ∀ who : P,
            Fintype (Option ((graphMachine g hctx).Action who)) :=
          fun who => graphMachine.instFintypeOptionAction g hctx LF who
        letI : Fintype (graphMachine g hctx).Event :=
          graphMachine.instFintypeEvent g hctx LF
        letI :
            Fintype
              ((graphMachine g hctx).BoundedRunPrefix
                (syntaxSteps g.prog)) :=
          Machine.BoundedRunPrefix.instFintype
        letI : DecidablePred
            (((fosgView g hctx).toBoundedFOSG
              (syntaxSteps g.prog)).terminal) :=
          Classical.decPred _
        exact
          (fosgView g hctx).boundedOutcomeFromBehavioral
            (syntaxSteps g.prog) β (syntaxSteps g.prog)) := rfl

end Vegas
