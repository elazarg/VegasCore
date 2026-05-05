import Vegas.Config
import Vegas.Protocol.SyntaxGraph

/-!
# Strategic kernel games

This module exposes the canonical finite strategic forms of checked Vegas
programs.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Pure strategy carrier at the program's finite syntax horizon. -/
abbrev pureStrategyAt
    (g : WFProgram P L) (who : P) : Type :=
  (syntaxGraphFOSGView g).BoundedPureStrategy (syntaxSteps g.prog) who

/-- Pure profile carrier at the program's finite syntax horizon. -/
abbrev pureProfileAt
    (g : WFProgram P L) : Type :=
  (syntaxGraphFOSGView g).BoundedPureProfile (syntaxSteps g.prog)

/-- PMF behavioral strategy carrier at the program's finite syntax horizon. -/
abbrev behavioralStrategyPMFAt
    (g : WFProgram P L) (who : P) : Type :=
  (syntaxGraphFOSGView g).BoundedBehavioralStrategy (syntaxSteps g.prog) who

/-- PMF behavioral profile carrier at the program's finite syntax horizon. -/
abbrev behavioralProfilePMFAt
    (g : WFProgram P L) : Type :=
  (syntaxGraphFOSGView g).BoundedBehavioralProfile (syntaxSteps g.prog)

/-- Outcome kernel of the finite pure strategic form of a checked Vegas
program. -/
noncomputable def pureOutcomeKernelAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) : PMF (Outcome P) := by
  classical
  exact
    (syntaxGraphFOSGView g).boundedOutcomeFromPure
      (syntaxSteps g.prog) π (syntaxSteps g.prog)

/-- Outcome kernel of the finite PMF behavioral strategic form of a checked
Vegas program. -/
noncomputable def behavioralOutcomeKernelPMFAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) : PMF (Outcome P) := by
  classical
  exact
    (syntaxGraphFOSGView g).boundedOutcomeFromBehavioral
      (syntaxSteps g.prog) β (syntaxSteps g.prog)

/-- Finite pure strategic form of a checked Vegas program. -/
noncomputable def pureKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P where
  Strategy := pureStrategyAt g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := pureOutcomeKernelAt g

@[simp] theorem pureKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pureKernelGameAt g).Strategy = pureStrategyAt g := rfl

@[simp] theorem pureKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    (pureKernelGameAt g).outcomeKernel π = pureOutcomeKernelAt g π := rfl

/-- Finite pure strategies for the public pure kernel game. -/
noncomputable instance pureKernelGameAt.instFintypeStrategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((pureKernelGameAt g).Strategy who) := by
  classical
  change Fintype (pureStrategyAt g who)
  dsimp [pureStrategyAt, Machine.FOSGView.BoundedPureStrategy]
  infer_instance

/-- Finite PMF behavioral strategic form of a checked Vegas program. -/
noncomputable def pmfBehavioralKernelGameAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.KernelGame P where
  Strategy := behavioralStrategyPMFAt g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := behavioralOutcomeKernelPMFAt g

@[simp] theorem pmfBehavioralKernelGameAt_Strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (pmfBehavioralKernelGameAt g).Strategy =
      behavioralStrategyPMFAt g := rfl

@[simp] theorem pmfBehavioralKernelGameAt_outcomeKernel
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    (pmfBehavioralKernelGameAt g).outcomeKernel β =
      behavioralOutcomeKernelPMFAt g β := rfl

end Vegas
