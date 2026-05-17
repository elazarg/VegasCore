import Vegas.Core.Finite
import Vegas.Core.ToEventGraph
import Vegas.EventGraph.RoundView

/-!
# Native strategic views of checked Vegas programs

This module is the Vegas-facing strategic layer before FOSG/EFG translation.
Strategies and kernels are defined from the event-graph machine's native round
view.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Native round view of the program event-graph machine. -/
noncomputable def eventGraphRoundView
    (g : WFProgram P L) :
    (eventGraphMachine g).RoundView :=
  (programEventGraph g).toRoundView (eventGraphMachineInterface g)
    (programEventGraph_hasIndependentFrontierRounds g)

/-- Finite state helper for the native program event-graph round view. -/
@[reducible] noncomputable instance eventGraphRoundView.instFintypeState
    (g : WFProgram P L) [FiniteDomains g] :
    Fintype (eventGraphMachine g).State := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  dsimp [eventGraphMachine, EventGraph.toMachine,
    programEventGraph, EventGraph.Configuration,
    EventGraph.ResultAssignment, EventGraph.FieldPatch]
  infer_instance

/-- Finite native round-action helper for event-graph round views. -/
@[reducible] noncomputable instance eventGraphRoundView.instFintypeAct
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((eventGraphRoundView g).Act who) := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  haveI : Fintype (programEventGraph g).Node := by
    change Fintype (ProgramNode g.prog)
    exact ProgramNode.instFintype g.prog
  haveI : Fintype (programEventGraph g).Field := by
    change Fintype (ProgramField g.prog)
    exact ProgramField.instFintype g.prog
  haveI :
      ∀ field : (programEventGraph g).Field,
        Fintype (L.Val ((programEventGraph g).fieldTy field)) := by
    intro field
    change Fintype (L.Val field.ty)
    exact ProgramField.instFintypeValue g field
  change Fintype (EventGraph.PlayerRoundAction (programEventGraph g) who)
  exact EventGraph.PlayerRoundAction.instFintype (programEventGraph g) who

/-- Finite optional native round-action helper for event-graph round views. -/
@[reducible] noncomputable instance eventGraphRoundView.instFintypeOptionAct
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype (Option ((eventGraphRoundView g).Act who)) := by
  classical
  letI : Fintype ((eventGraphRoundView g).Act who) :=
    eventGraphRoundView.instFintypeAct g who
  infer_instance

/-- Pure strategy carrier at the program's finite syntax horizon. -/
abbrev pureStrategyAt
    (g : WFProgram P L) (who : P) : Type :=
  (eventGraphRoundView g).BoundedPureStrategy (syntaxSteps g.prog) who

/-- Pure profile carrier at the program's finite syntax horizon. -/
abbrev pureProfileAt
    (g : WFProgram P L) : Type :=
  (eventGraphRoundView g).BoundedPureProfile (syntaxSteps g.prog)

/-- PMF behavioral strategy carrier at the program's finite syntax horizon. -/
abbrev behavioralStrategyPMFAt
    (g : WFProgram P L) (who : P) : Type :=
  (eventGraphRoundView g).BoundedBehavioralStrategy (syntaxSteps g.prog) who

/-- PMF behavioral profile carrier at the program's finite syntax horizon. -/
abbrev behavioralProfilePMFAt
    (g : WFProgram P L) : Type :=
  (eventGraphRoundView g).BoundedBehavioralProfile (syntaxSteps g.prog)

end Vegas
