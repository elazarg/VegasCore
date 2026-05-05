import Vegas.Config
import Vegas.Protocol.SyntaxGraph

/-!
# Strategic kernel games

This module exposes the canonical finite graph-native syntax-machine FOSG
strategic forms.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Pure strategy carrier of the finite graph-machine FOSG at the program's
syntax horizon. -/
abbrev pureStrategyAt
    (g : WFProgram P L) (who : P) : Type :=
  (syntaxGraphFOSGView g).BoundedPureStrategy (syntaxSteps g.prog) who

/-- Pure profile carrier of the finite graph-machine FOSG. -/
abbrev pureProfileAt
    (g : WFProgram P L) : Type :=
  (syntaxGraphFOSGView g).BoundedPureProfile (syntaxSteps g.prog)

/-- PMF behavioral strategy carrier of the finite graph-machine FOSG at the
program's syntax horizon. -/
abbrev behavioralStrategyPMFAt
    (g : WFProgram P L) (who : P) : Type :=
  (syntaxGraphFOSGView g).BoundedBehavioralStrategy (syntaxSteps g.prog) who

/-- PMF behavioral profile carrier of the finite graph-machine FOSG. -/
abbrev behavioralProfilePMFAt
    (g : WFProgram P L) : Type :=
  (syntaxGraphFOSGView g).BoundedBehavioralProfile (syntaxSteps g.prog)

/-- Finite FOSG-native pure strategic form of a checked Vegas program. -/
noncomputable def pureKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P where
  Strategy := pureStrategyAt g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun π => by
    classical
    letI : Fintype (syntaxGraphMachine g).State :=
      syntaxGraphMachine.instFintypeState g
    letI : ∀ who : P,
        Fintype (Option ((syntaxGraphMachine g).Action who)) :=
      fun who => syntaxGraphMachine.instFintypeOptionAction g who
    letI : Fintype (syntaxGraphMachine g).Event :=
      syntaxGraphMachine.instFintypeEvent g
    letI :
        Fintype
          ((syntaxGraphMachine g).BoundedRunPrefix
            (syntaxSteps g.prog)) :=
      Machine.BoundedRunPrefix.instFintype
    letI : DecidablePred
        (((syntaxGraphFOSGView g).toBoundedFOSG
          (syntaxSteps g.prog)).terminal) :=
      Classical.decPred _
    exact
      (syntaxGraphFOSGView g).boundedOutcomeFromPure
        (syntaxSteps g.prog) π (syntaxSteps g.prog)

@[simp] theorem pureKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGameAt g).Strategy = pureStrategyAt g := rfl

@[simp] theorem pureKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    (pureKernelGameAt g).outcomeKernel π =
      (by
        classical
        letI : Fintype (syntaxGraphMachine g).State :=
          syntaxGraphMachine.instFintypeState g
        letI : ∀ who : P,
            Fintype (Option ((syntaxGraphMachine g).Action who)) :=
          fun who => syntaxGraphMachine.instFintypeOptionAction g who
        letI : Fintype (syntaxGraphMachine g).Event :=
          syntaxGraphMachine.instFintypeEvent g
        letI :
            Fintype
              ((syntaxGraphMachine g).BoundedRunPrefix
                (syntaxSteps g.prog)) :=
          Machine.BoundedRunPrefix.instFintype
        letI : DecidablePred
            (((syntaxGraphFOSGView g).toBoundedFOSG
              (syntaxSteps g.prog)).terminal) :=
          Classical.decPred _
        exact
          (syntaxGraphFOSGView g).boundedOutcomeFromPure
            (syntaxSteps g.prog) π (syntaxSteps g.prog)) := rfl

/-- Finite pure strategies for the public pure kernel game. The implementation
uses the graph-machine FOSG finite-history package, but the instance head is
the Vegas kernel-game strategy carrier. -/
noncomputable instance pureKernelGameAt.instFintypeStrategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((pureKernelGameAt g).Strategy who) := by
  classical
  letI : Fintype (syntaxGraphMachine g).State :=
    syntaxGraphMachine.instFintypeState g
  letI : ∀ who : P,
      Fintype (Option ((syntaxGraphMachine g).Action who)) :=
    fun who => syntaxGraphMachine.instFintypeOptionAction g who
  letI : Fintype (syntaxGraphMachine g).Event :=
    syntaxGraphMachine.instFintypeEvent g
  letI :
      Fintype
        ((syntaxGraphMachine g).BoundedRunPrefix
          (syntaxSteps g.prog)) :=
    Machine.BoundedRunPrefix.instFintype
  letI : Fintype
      (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).History) :=
    syntaxGraphFOSGView.instFintypeBoundedHistory g (syntaxSteps g.prog)
  dsimp [pureKernelGameAt, pureStrategyAt,
    Machine.FOSGView.BoundedPureStrategy]
  infer_instance

/-- Finite FOSG-native PMF behavioral strategic form of a checked Vegas
program. -/
noncomputable def pmfBehavioralKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun β => by
    classical
    letI : Fintype (syntaxGraphMachine g).State :=
      syntaxGraphMachine.instFintypeState g
    letI : ∀ who : P,
        Fintype (Option ((syntaxGraphMachine g).Action who)) :=
      fun who => syntaxGraphMachine.instFintypeOptionAction g who
    letI : Fintype (syntaxGraphMachine g).Event :=
      syntaxGraphMachine.instFintypeEvent g
    letI :
        Fintype
          ((syntaxGraphMachine g).BoundedRunPrefix
            (syntaxSteps g.prog)) :=
      Machine.BoundedRunPrefix.instFintype
    letI : DecidablePred
        (((syntaxGraphFOSGView g).toBoundedFOSG
          (syntaxSteps g.prog)).terminal) :=
      Classical.decPred _
    exact
      (syntaxGraphFOSGView g).boundedOutcomeFromBehavioral
        (syntaxSteps g.prog) β (syntaxSteps g.prog)

@[simp] theorem pmfBehavioralKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

@[simp] theorem pmfBehavioralKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    (pmfBehavioralKernelGameAt g).outcomeKernel β =
      (by
        classical
        letI : Fintype (syntaxGraphMachine g).State :=
          syntaxGraphMachine.instFintypeState g
        letI : ∀ who : P,
            Fintype (Option ((syntaxGraphMachine g).Action who)) :=
          fun who => syntaxGraphMachine.instFintypeOptionAction g who
        letI : Fintype (syntaxGraphMachine g).Event :=
          syntaxGraphMachine.instFintypeEvent g
        letI :
            Fintype
              ((syntaxGraphMachine g).BoundedRunPrefix
                (syntaxSteps g.prog)) :=
          Machine.BoundedRunPrefix.instFintype
        letI : DecidablePred
            (((syntaxGraphFOSGView g).toBoundedFOSG
              (syntaxSteps g.prog)).terminal) :=
          Classical.decPred _
        exact
          (syntaxGraphFOSGView g).boundedOutcomeFromBehavioral
            (syntaxSteps g.prog) β (syntaxSteps g.prog)) := rfl

end Vegas
