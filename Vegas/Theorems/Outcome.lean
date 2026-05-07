import Vegas.Protocol.Strategic

/-!
# Outcome Adequacy Theorems

Project-facing names for the connection between terminal syntax-graph states,
declared payoff expressions, and strategic-form outcome kernels.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Terminal syntax-graph configurations assemble the final source environment
used by payoff evaluation. -/
theorem checkedProgram_terminalFinalEnv_isSome
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    (hterminal : cfg.terminal) :
    (ProgramField.finalEnv? g.prog (syntaxGraphConfigValue? g cfg)).isSome :=
  syntaxGraph_finalEnv?_isSome_of_terminal g hterminal

/-- Terminal syntax-graph outcomes are the declared payoff expressions evaluated
in the assembled final source environment. -/
theorem checkedProgram_terminalOutcome_eq_evalPayoffs
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    (hterminal : cfg.terminal) :
    ∃ env : VEnv L (ProgramField.finalVCtx g.prog),
      ProgramField.finalEnv? g.prog (syntaxGraphConfigValue? g cfg) = some env ∧
        syntaxGraphOutcome g cfg =
          evalPayoffs (ProgramField.finalPayoffs g.prog) env :=
  syntaxGraphOutcome_eq_evalPayoffs_of_terminal g hterminal

/-- A checked game that is played legally to completion reaches its declared
payoff rule. -/
theorem checkedProgram_wholeGame_reaches_declared_payoff_rule
    (g : WFProgram P L)
    (h :
      (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).History))
    (hcomplete :
      ((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).terminal h.lastState) :
    ∃ env : VEnv L (ProgramField.finalVCtx g.prog),
      ProgramField.finalEnv? g.prog
          (syntaxGraphConfigValue? g h.lastState.state) = some env ∧
        syntaxGraphOutcome g h.lastState.state =
          evalPayoffs (ProgramField.finalPayoffs g.prog) env :=
  syntaxGraph_wholeGame_reaches_declared_payoff_rule g h hcomplete

/-- Pure strategic-form outcomes are exactly the syntax-graph machine blocked
trace outcomes projected to payoff outcomes. -/
theorem checkedProgram_pureOutcome_eq_blockTrace
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    pureOutcomeKernelAt g π =
      PMF.map
        (syntaxGraphTraceOutcome g)
        (syntaxGraphFOSGBlockTraceDistFrom g (syntaxSteps g.prog)
          (GameTheory.FOSG.legalPureToBehavioral
            ((syntaxGraphFOSGView g).toBoundedFOSG (syntaxSteps g.prog))
            π.extend)
          (syntaxSteps g.prog)
          (syntaxGraphInitialHistory g (syntaxSteps g.prog))) :=
  pureOutcomeKernelAt_eq_blockTraceDist g π

/-- PMF behavioral strategic-form outcomes are exactly the syntax-graph machine
blocked trace outcomes projected to payoff outcomes. -/
theorem checkedProgram_behavioralOutcome_eq_blockTrace
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    behavioralOutcomeKernelPMFAt g β =
      PMF.map
        (syntaxGraphTraceOutcome g)
        (syntaxGraphFOSGBlockTraceDistFrom g (syntaxSteps g.prog)
          β.extend
          (syntaxSteps g.prog)
          (syntaxGraphInitialHistory g (syntaxSteps g.prog))) :=
  behavioralOutcomeKernelPMFAt_eq_blockTraceDist g β

end Vegas
