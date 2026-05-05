import Vegas.Protocol.Checked

/-!
# Strategic kernel games

This module exposes the canonical finite graph-machine FOSG strategic forms.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Pure strategy carrier of the finite graph-machine FOSG at the program's
syntax horizon. -/
abbrev pureStrategyAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) : Type :=
  (fosgView g hctx).BoundedPureStrategy (syntaxSteps g.prog) who

/-- Pure profile carrier of the finite graph-machine FOSG. -/
abbrev pureProfileAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Type :=
  (fosgView g hctx).BoundedPureProfile (syntaxSteps g.prog)

/-- PMF behavioral strategy carrier of the finite graph-machine FOSG at the
program's syntax horizon. -/
abbrev behavioralStrategyPMFAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) : Type :=
  (fosgView g hctx).BoundedBehavioralStrategy (syntaxSteps g.prog) who

/-- PMF behavioral profile carrier of the finite graph-machine FOSG. -/
abbrev behavioralProfilePMFAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Type :=
  (fosgView g hctx).BoundedBehavioralProfile (syntaxSteps g.prog)

/-- Finite FOSG-native pure strategic form of a checked Vegas program. -/
noncomputable def pureKernelGameAt
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) : GameTheory.KernelGame P where
  Strategy := pureStrategyAt g hctx
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

@[simp] theorem pureKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) :
    (pureKernelGameAt g hctx LF).Strategy =
      pureStrategyAt g hctx := rfl

@[simp] theorem pureKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) (π : pureProfileAt g hctx) :
    (pureKernelGameAt g hctx LF).outcomeKernel π =
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
noncomputable def pmfBehavioralKernelGameAt
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) : GameTheory.KernelGame P where
  Strategy := behavioralStrategyPMFAt g hctx
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

@[simp] theorem pmfBehavioralKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) :
    (pmfBehavioralKernelGameAt g hctx LF).Strategy =
      behavioralStrategyPMFAt g hctx := rfl

@[simp] theorem pmfBehavioralKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) (β : behavioralProfilePMFAt g hctx) :
    (pmfBehavioralKernelGameAt g hctx LF).outcomeKernel β =
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
