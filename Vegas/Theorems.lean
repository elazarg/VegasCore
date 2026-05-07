import Vegas.ProtocolSemantics
import Vegas.Protocol.Backend

/-!
# Project theorem index

This file collects the main Vegas semantic claims under short project-facing
names. The proofs here are intentionally shallow wrappers over the files that
own the substantive arguments.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Checked-program execution -/

/-- A nonterminal protocol-graph configuration has a nonempty executable
frontier. This is the graph-level progress theorem. -/
theorem protocolGraph_frontier_nonempty_of_not_terminal
    {G : ProtocolGraph P L} {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    cfg.frontier.Nonempty :=
  cfg.frontier_nonempty_of_not_terminal hterminal

/-- Checked source graphs have at least one legal concrete action for every
player-owned frontier node. -/
theorem checkedProgram_hasAvailablePlayerActions
    (g : WFProgram P L) :
    (syntaxProtocolGraph g).HasAvailablePlayerActions :=
  syntaxProtocolGraph_hasAvailablePlayerActions g

/-- Checked source graphs admit stable frontier rounds: executing one frontier
node cannot invalidate another source-legal frontier action. -/
theorem checkedProgram_hasStableFrontierRounds
    (g : WFProgram P L) :
    (syntaxProtocolGraph g).HasStableFrontierRounds :=
  syntaxProtocolGraph_hasStableFrontierRounds g

/-- The bounded syntax-graph FOSG view has the legal-observability property
needed by Kuhn realization. -/
theorem checkedProgram_boundedFOSG_legalObservable
    (g : WFProgram P L) (horizon : Nat) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).LegalObservable :=
  syntaxGraphFOSGView_toBoundedFOSG_legalObservable g horizon

/-! ## Outcome adequacy -/

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

/-! ## Realization -/

/-- Finite checked Vegas programs satisfy mixed-to-PMF-behavioral realization
over the project kernel-game carriers. -/
theorem checkedProgram_kuhnPMF
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    KuhnPMF g :=
  kuhnPMF_finite g

/-- Independent mixed profiles over pure strategies have PMF behavioral
realizations with the same payoff-outcome distribution. -/
theorem checkedProgram_mixed_to_behavioral
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (μ : ∀ who, PMF ((pureKernelGameAt g).Strategy who)) :
    ∃ β : (pmfBehavioralKernelGameAt g).Profile,
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g).outcomeKernel π) :=
  kuhn_finite g μ

/-! ## Backend refinement -/

omit [DecidableEq P] in
/-- Compatible backend block laws preserve blocked trace distributions after
projection to the specification machine. -/
theorem backend_blockTraceDist_project_eq
    {Impl Spec : Machine P}
    (R : Machine.StochasticStepRefinement Impl Spec)
    (lawSpec : Spec.BlockLaw) (lawImpl : Impl.BlockLaw)
    (compat : R.BlockLawCompatible lawImpl lawSpec)
    (horizon : Nat) (trace : Impl.BlockTrace) :
    PMF.map R.projectBlockTrace
        (Impl.blockTraceDistFrom lawImpl horizon trace) =
      Spec.blockTraceDistFrom lawSpec horizon (R.projectBlockTrace trace) :=
  R.blockTraceDist_project_eq lawSpec lawImpl compat horizon trace

end Vegas
