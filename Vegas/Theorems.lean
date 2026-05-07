import Vegas.ProtocolSemantics
import Vegas.Protocol.Backend
import Vegas.Protocol.LinearRead
import Vegas.Protocol.StateSufficiency

/-!
# Project theorem index

This file collects the main Vegas semantic claims under short project-facing
names. The proofs here are intentionally shallow wrappers over the files that
own the substantive arguments.

The Vegas soundness facts collected here are operational and informational:
checked games have legal continuations at nonterminal states, bounded
presentations reach their horizon, and player-facing menus are determined by
the observations available to the acting player.
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
node preserves source-legal frontier actions for the remaining frontier. -/
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

/-! ## Execution and observation soundness -/

/-- Source-linear reading has a ready next event whenever the syntax graph is
nonterminal. -/
theorem checkedProgram_linearRead_sufficient
    (g : WFProgram P L)
    (cfg : (syntaxProtocolGraph g).Configuration)
    (hterminal : ¬ cfg.terminal) :
    ∃ node : ProgramNode g.prog,
      node ∈ cfg.frontier ∧
        ∀ other : ProgramNode g.prog,
          other ∈ ProgramNode.finset g.prog →
            (cfg.result other).isNone →
              node.rank ≤ other.rank :=
  syntaxLinearRead_sufficient g cfg hterminal

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

/-- Omniscient progress for the bounded syntax-graph FOSG: every nonterminal
state admits at least one legal joint action. -/
theorem checkedProgram_boundedFOSG_exists_legal_of_not_terminal
    (g : WFProgram P L) (horizon : Nat)
    {state : (syntaxGraphMachine g).BoundedState horizon}
    (hterminal :
      ¬ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal state) :
    ∃ action : JointAction (syntaxGraphFOSGView g).Act,
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).legal state action :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).exists_legal_of_not_terminal
    hterminal

/-- The bounded syntax-graph FOSG reaches terminal/cutoff by its presentation
horizon. -/
theorem checkedProgram_boundedFOSG_boundedHorizon
    (g : WFProgram P L) (horizon : Nat) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).BoundedHorizon horizon :=
  (syntaxGraphFOSGView g).toBoundedFOSG_boundedHorizon horizon

/-- Terminal bounded syntax-graph FOSG states have no legal joint action. -/
theorem checkedProgram_boundedFOSG_not_legal_of_terminal
    (g : WFProgram P L) (horizon : Nat)
    {state : (syntaxGraphMachine g).BoundedState horizon}
    {action : JointAction (syntaxGraphFOSGView g).Act}
    (hterminal :
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal state) :
    ¬ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).legal state action :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).not_legal_of_terminal
    hterminal

/-- Joint-action legality in the bounded syntax-graph FOSG decomposes into
nonterminality and per-player local optional-move legality. -/
theorem checkedProgram_boundedFOSG_legal_iff_forall_locallyLegal
    (g : WFProgram P L) (horizon : Nat)
    {state : (syntaxGraphMachine g).BoundedState horizon}
    {action : JointAction (syntaxGraphFOSGView g).Act} :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).legal state action ↔
      ¬ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal state ∧
        ∀ who,
          ((syntaxGraphFOSGView g).toBoundedFOSG horizon).locallyLegalAtState
            state who (action who) :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).legal_iff_forall

/-- A player's whole frontier-round optional menu is determined by the public
transcript together with that player's private observation. -/
theorem checkedProgram_roundMenu_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpriv : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right) :
    ProtocolGraph.roundMenu (syntaxProtocolGraph g) left who =
      ProtocolGraph.roundMenu (syntaxProtocolGraph g) right who :=
  syntaxGraph_roundMenu_eq_of_observation_eq g who hpriv hpub

/-- Membership in a player's frontier-round menu is transported across equal
public transcript and private observation. -/
theorem checkedProgram_roundMenu_mem_iff_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpriv : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right)
    (move :
      Option (ProtocolGraph.PlayerRoundAction (syntaxProtocolGraph g) who)) :
    move ∈ ProtocolGraph.roundMenu (syntaxProtocolGraph g) left who ↔
      move ∈ ProtocolGraph.roundMenu (syntaxProtocolGraph g) right who := by
  rw [checkedProgram_roundMenu_eq_of_observation_eq g who hpriv hpub]

/-- At the current bounded FOSG history endpoint, a player's available optional
moves are determined by the current private and public observations, provided
both histories are before the presentation cutoff. -/
theorem checkedProgram_availableMoves_eq_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      syntaxGraphObserve g who h.lastState.state =
        syntaxGraphObserve g who h'.lastState.state)
    (hpub :
      syntaxGraphPublicView g h.lastState.state =
        syntaxGraphPublicView g h'.lastState.state) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who :=
  syntaxGraph_availableMoves_eq_of_currentObservation_eq
    g horizon who hcut hcut' hpriv hpub

/-- Membership in the current optional move set is transported by equality of
current private and public observations. -/
theorem checkedProgram_availableMoves_mem_iff_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      syntaxGraphObserve g who h.lastState.state =
        syntaxGraphObserve g who h'.lastState.state)
    (hpub :
      syntaxGraphPublicView g h.lastState.state =
        syntaxGraphPublicView g h'.lastState.state)
    (move : Option ((syntaxGraphFOSGView g).Act who)) :
    move ∈ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who ↔
      move ∈
        ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  rw [checkedProgram_availableMoves_eq_of_currentObservation_eq
    g horizon who hcut hcut' hpriv hpub]

/-- For nonempty bounded FOSG histories before cutoff, equality of latest
private/public observations determines a player's whole optional move set. -/
theorem checkedProgram_availableMoves_eq_of_latestObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hne : h.steps ≠ [])
    (hne' : h'.steps ≠ [])
    (hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h'.playerView who)) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who :=
  syntaxGraph_availableMoves_eq_of_latestObservation_eq
    g horizon who hcut hcut' hne hne' hlatest

/-- Membership in the current optional move set is transported by equality of
latest private/public observations. -/
theorem checkedProgram_availableMoves_mem_iff_of_latestObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hne : h.steps ≠ [])
    (hne' : h'.steps ≠ [])
    (hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h'.playerView who))
    (move : Option ((syntaxGraphFOSGView g).Act who)) :
    move ∈ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who ↔
      move ∈
        ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  rw [checkedProgram_availableMoves_eq_of_latestObservation_eq
    g horizon who hcut hcut' hne hne' hlatest]

/-- Equal FOSG player views determine equal concrete action sets at histories. -/
theorem checkedProgram_availableActions_eq_of_playerView_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hinfo : h.playerView who = h'.playerView who) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActionsAtHistory
        h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActionsAtHistory
        h' who :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActions_eq_of_playerView_eq
    (checkedProgram_boundedFOSG_legalObservable g horizon) who hinfo

/-- The optional move set attached to a reachable information state is the same
as the optional move set at any history realizing that information state. -/
theorem checkedProgram_availableMovesAtInfoState_eq_of_history
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtInfoState
        who (h.playerView who) =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtInfoState_eq_of_history
    (checkedProgram_boundedFOSG_legalObservable g horizon) who h

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
