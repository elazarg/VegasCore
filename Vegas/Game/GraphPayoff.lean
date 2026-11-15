module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ProgramPaymentNash
public import Vegas.Source.Utility
public import Vegas.EventGraph.RankedConfig
public import Vegas.EventGraph.SequentialLaw

@[expose] public section

/-! # Source readout and fixed-exit utility for arbitrary valid dependencies

The compiled event code is fixed. These readers interpret complete configurations
in source rank, while the dependency choice controls only when events may run.
Canonical comparison requires no additional information-order hypothesis.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A player's payoff under the supplied dependencies: the exclusion utility of the
outcome read with default entries in instruction order, or the excluded payoff
before the run ends. -/
def graphPayoff (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (config : (setup.dataflowGraph.withDependencies
      deps).Config) :
    ℝ :=
  if terminal : config.cut.Terminal then
    exclusionUtility setup.program excludedPayoff utility
      (setup.eventParameterOutcome parameter
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) config terminal,
          rankedConfig_terminal
            (graph := (setup.dataflowGraph.withDependencies deps)) config terminal⟩) who
  else excludedPayoff who

theorem graphPayoff_factors (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (left right :
      (setup.dataflowGraph.withDependencies deps).Config)
    (same : runKey left = runKey right) :
    setup.graphPayoff deps parameter utility excludedPayoff who left =
      setup.graphPayoff deps parameter utility excludedPayoff who right := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  unfold graphPayoff
  by_cases terminal : left.cut.Terminal
  · have rightTerminal : right.cut.Terminal := cut ▸ terminal
    rw [dite_eq_left terminal, dite_eq_left rightTerminal]
    have outcome : (⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) left
      terminal,
        rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) left terminal⟩
          :
          {config : setup.informationGraph.Config // config.cut.Terminal}) =
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) right rightTerminal,
          rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) right
            rightTerminal⟩ :=
      Subtype.ext (rankedConfig_congr (graph := (setup.dataflowGraph.withDependencies deps)) same
        terminal
          rightTerminal)
    rw [outcome]
  · have rightTerminal : ¬ right.cut.Terminal := cut ▸ terminal
    rw [dite_eq_right terminal, dite_eq_right rightTerminal]

theorem graphPayoff_of_defaulted (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (config : (setup.dataflowGraph.withDependencies
      deps).Config)
    (defaulted : who ∈ config.defaulted) :
    setup.graphPayoff deps parameter utility excludedPayoff who config = excludedPayoff who := by
  unfold graphPayoff
  by_cases terminal : config.cut.Terminal
  · rw [dite_eq_left terminal]
    apply exclusionUtility_of_defaulted
    change who ∈ (rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) config
      terminal).defaulted
    rw [defaulted_rankedConfig]
    exact defaulted
  · rw [dite_eq_right terminal]

theorem le_graphPayoff (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    (low : ∀ outcome, excludedPayoff who ≤ utility outcome who)
    (config : (setup.dataflowGraph.withDependencies deps).Config) :
    excludedPayoff who ≤ setup.graphPayoff deps parameter utility excludedPayoff who config := by
  unfold graphPayoff exclusionUtility
  split
  · split
    · exact le_rfl
    · exact low _
  · exact le_rfl

/-- The initial law of a dependency graph: the setup draw, encoded as inputs. -/
abbrev graphInputs (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) :
    PMF (setup.dataflowGraph.withDependencies deps).Inputs :=
  setup.initialLaw.map fun initial => setup.eventInputs initial

theorem graphInputs_support_finite (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    [setup.FiniteInitialLaw] : (setup.graphInputs deps).support.Finite := by
  rw [PMF.support_map]
  exact setup.initialLaw_support_finite.image _

theorem graphRun_support_finite (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : (setup.dataflowGraph.withDependencies deps).BehavioralProfile)
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler) :
    ((setup.graphInputs deps).bind
      ((setup.dataflowGraph.withDependencies deps).runPolicies scheduler profile)).support.Finite
        := by
  rw [PMF.support_bind]
  exact (setup.graphInputs_support_finite deps).biUnion fun initial _ =>
    (setup.dataflowGraph.withDependencies deps).runPolicies_support_finite scheduler profile
      ((toInformationGraph_finiteActions setup.program finite).profileFiniteSupport profile) initial

/-- The terminal source configuration of a graph play, read in instruction order. -/
def graphReadout (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (outcome : (setup.dataflowGraph.withDependencies deps).gameSignature.Outcome) :
    Config Player L setup.program.terminalCtx :=
  terminalConfig setup.program
    ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
      rankedConfig_terminal
        (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2⟩

/-- The source-order readout and payoffs of a graph configuration. -/
def graphObservation (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (config : (setup.dataflowGraph.withDependencies deps).Config) :
    Option (Config Player L setup.program.terminalCtx) × (Player → ℝ) :=
  (if terminal : config.cut.Terminal then
      some (terminalConfig setup.program
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) config terminal,
          rankedConfig_terminal
            (graph := (setup.dataflowGraph.withDependencies deps)) config terminal⟩)
    else none,
    fun who => setup.graphPayoff deps parameter utility excludedPayoff who config)

theorem graphObservation_factors (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (left right : (setup.dataflowGraph.withDependencies deps).Config)
    (same : runKey left = runKey right) :
    setup.graphObservation deps parameter utility excludedPayoff left =
      setup.graphObservation deps parameter utility excludedPayoff right := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  unfold graphObservation
  refine Prod.ext ?_ (funext fun who =>
    setup.graphPayoff_factors deps parameter utility excludedPayoff who left right same)
  by_cases terminal : left.cut.Terminal
  · have rightTerminal : right.cut.Terminal := cut ▸ terminal
    simp only [dite_eq_left terminal, dite_eq_left rightTerminal]
    have outcome : (⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) left
      terminal,
        rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) left terminal⟩
          :
          {config : setup.informationGraph.Config // config.cut.Terminal}) =
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) right rightTerminal,
          rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) right
            rightTerminal⟩ :=
      Subtype.ext (rankedConfig_congr (graph := (setup.dataflowGraph.withDependencies deps)) same
        terminal
          rightTerminal)
    rw [outcome]
  · have rightTerminal : ¬ right.cut.Terminal := cut ▸ terminal
    simp only [dite_eq_right terminal, dite_eq_right rightTerminal]


/-- Canonical execution has the joint source-order configuration and fixed-exit
payoff law of the compiled source-information game, for every dependency choice
and arbitrary setup initial law. -/
theorem canonical_graphObservation_law (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (profile : setup.informationGraph.BehavioralProfile) :
    ((setup.graphInputs deps).bind ((setup.dataflowGraph.withDependencies deps).runPolicies
        (setup.dataflowGraph.withDependencies deps).canonicalScheduler profile)).map
        (setup.graphObservation deps parameter utility excludedPayoff) =
      (setup.canonicalEventGame.play profile).map fun outcome =>
        (some (terminalConfig setup.program outcome), fun who =>
          exclusionUtility setup.program excludedPayoff utility
            (setup.eventParameterOutcome parameter outcome) who) := by
  let readout : setup.informationGraph.Config →
      Option (Config Player L setup.program.terminalCtx) × (Player → ℝ) := fun config =>
    if terminal : config.cut.Terminal then
      (some (terminalConfig setup.program ⟨config, terminal⟩), fun who =>
        exclusionUtility setup.program excludedPayoff utility
          (setup.eventParameterOutcome parameter ⟨config, terminal⟩) who)
    else (none, fun who => excludedPayoff who)
  have play : setup.canonicalEventGame.play profile = (setup.graphInputs deps).bind
      (setup.informationGraph.terminalOutcomes setup.informationGraph.canonicalScheduler profile)
        := rfl
  rw [play, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  have law := (setup.dataflowGraph.withDependencies deps).canonical_fromSequential_config_law
    profile initial
  have outcomes : (setup.informationGraph.terminalOutcomes
      setup.informationGraph.canonicalScheduler profile initial).map
        (fun outcome => (some (terminalConfig setup.program outcome), fun who =>
          exclusionUtility setup.program excludedPayoff utility
            (setup.eventParameterOutcome parameter outcome) who)) =
      (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler profile
        initial).map readout := by
    rw [← setup.informationGraph.terminalOutcomes_map_val, PMF.map_comp]
    apply map_congr_on_support _
    intro outcome _
    simp only [Function.comp_apply, readout, dite_eq_left outcome.2, Subtype.coe_eta]
  refine Eq.trans ?_ outcomes.symm
  rw [← law, PMF.map_comp]
  apply map_congr_on_support _
  intro config member
  have reach := setup.informationGraph.run_reachable initial _ config member
  have terminal := setup.informationGraph.runPolicies_terminal _ profile initial config member
  have viewTerminal : ((setup.dataflowGraph.withDependencies deps).fromSequentialConfig
      config).cut.Terminal := terminal
  have recast := rankedConfig_fromSequentialConfig
    (graph := setup.dataflowGraph.withDependencies deps) reach viewTerminal
  have outcome : (⟨rankedConfig (graph := setup.dataflowGraph.withDependencies deps)
      ((setup.dataflowGraph.withDependencies deps).fromSequentialConfig config) viewTerminal,
      rankedConfig_terminal (graph := setup.dataflowGraph.withDependencies deps) _ viewTerminal⟩ :
      {config : setup.informationGraph.Config // config.cut.Terminal}) = ⟨config, terminal⟩ :=
    Subtype.ext recast
  simp only [Function.comp_apply, graphObservation, graphPayoff, readout,
    dite_eq_left viewTerminal, dite_eq_left terminal, outcome]

/-- Canonical expected fixed-exit payoff agrees with the compiled source-information
game, without finiteness or integrability premises. -/
theorem expect_graphPayoff_canonical
    (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    (profile : setup.informationGraph.BehavioralProfile) :
    expect ((setup.graphInputs deps).bind ((setup.dataflowGraph.withDependencies deps).runPolicies
        (setup.dataflowGraph.withDependencies deps).canonicalScheduler profile))
        (setup.graphPayoff deps parameter utility excludedPayoff who) =
      expect (setup.canonicalEventGame.play profile) fun outcome =>
        exclusionUtility setup.program excludedPayoff utility
          (setup.eventParameterOutcome parameter outcome) who := by
  let project : Option (Config Player L setup.program.terminalCtx) × (Player → ℝ) → ℝ :=
    fun observation => observation.2 who
  have law := congrArg (fun law => expect law project)
    (setup.canonical_graphObservation_law deps parameter utility excludedPayoff profile)
  simp only [expect_map, Function.comp_def, graphObservation, project] at law
  exact law


end Vegas.SourceProgram.Setup
