import Vegas.Core.ToEventGraph.Games
import Vegas.Core.ToEventGraph.SourceAdequacy

/-!
# Outcome adequacy

Compiled frontier outcomes agree with the source payoff projection on
reachable terminal graph states.  Completed frontier kernels are the native
round-view run distributions pushed through that projection.
-/

namespace Vegas

namespace ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Primitive-machine terminal outcomes agree with the source payoff
projection reconstructed from the terminal compiled store. -/
theorem primitiveOutcome_eq_sourceAtTerminal
    (program : GraphProgram P L)
    (state : (PrimitiveMachine (compile program)).State)
    (hterminal : (PrimitiveMachine (compile program)).terminal state) :
    (PrimitiveMachine (compile program)).outcome state =
      some (sourceOutcomeAtTerminal program state
        (by simpa [PrimitiveMachine, primitiveMachineSpec] using hterminal)) :=
  compile_primitiveMachine_outcome_eq_sourceAtTerminal
    program state hterminal

end ToEventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Pure completed-frontier outcome kernels are the completed run
distribution pushed through source payoff projection. -/
theorem pureFrontierOutcomeKernel_sourceMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.frontierSemantics.pure.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.pure.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          ((program.frontierSemantics.pure.view).legalPureToBehavioral
            (ToEventGraph.completionBound
              (ToEventGraph.compile program.core)) profile)) :=
  program.pureFrontierOptionOutcomeKernel_eq_sourceMap profile

/-- Behavioral completed-frontier outcome kernels are the completed run
distribution pushed through source payoff projection. -/
theorem behavioralFrontierOutcomeKernel_sourceMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierSemantics.behavioral.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.behavioral.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core)) profile) :=
  program.behavioralFrontierOptionOutcomeKernel_eq_sourceMap profile

end WFProgram

end Vegas
