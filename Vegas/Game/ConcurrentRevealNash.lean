module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.ConcurrentRevealGraph
public import Vegas.Game.ProgramPaymentNash
public import Vegas.Game.IntendedNash
public import Vegas.Source.Utility

@[expose] public section

/-! # Intended-game Nash equilibria under every schedule of concurrent reveals

Relax the reveal dependencies of the compiled graph, so that independent
reveals may complete in any order a public scheduler chooses. A player's payoff
reads the outcome with default entries in instruction order, and is the
excluded payoff once the player has defaulted. The compiled clients of a source
profile that discloses at every reveal and extends an `ε`-Nash equilibrium of
the intended game, normalized to ignore completion order, are an `ε`-Nash
equilibrium under every public scheduler.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The forfeiture interface admits every source policy. -/
theorem BehavioralPolicy.admitted_forfeiture {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) →
      policy.Admitted program (CommitmentInterface.forfeiture program)
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ next, policy => admitted_forfeiture next policy
  | _, _, .commit _ _ _ _ next, policy => by
      refine ⟨fun _ _ _ choice _ => ?_, admitted_forfeiture next policy.2⟩
      rcases choice with _ | _ | _
      · trivial
      · rfl
      · trivial
  | _, _, .reveal _ _ _ _ _ _ next, policy => admitted_forfeiture next policy.2

end Vegas.SourceProgram

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A player's payoff on the concurrent graph: the exclusion utility of the
outcome read with default entries in instruction order, or the excluded payoff
before the run ends. -/
def concurrentPayoff (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (config : setup.revealRelaxedGraph.Config) :
    ℝ :=
  if terminal : config.cut.Terminal then
    exclusionUtility setup.program excludedPayoff utility
      (setup.eventParameterOutcome parameter
        ⟨rankedConfig (graph := setup.revealRelaxedGraph) config terminal, rankedConfig_terminal
            (graph := setup.revealRelaxedGraph) config terminal⟩) who
  else excludedPayoff who

theorem concurrentPayoff_factors (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (left right : setup.revealRelaxedGraph.Config)
    (same : runKey left = runKey right) :
    setup.concurrentPayoff parameter utility excludedPayoff who left =
      setup.concurrentPayoff parameter utility excludedPayoff who right := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  unfold concurrentPayoff
  by_cases terminal : left.cut.Terminal
  · have rightTerminal : right.cut.Terminal := cut ▸ terminal
    rw [dite_eq_left terminal, dite_eq_left rightTerminal]
    have outcome : (⟨rankedConfig (graph := setup.revealRelaxedGraph) left terminal,
        rankedConfig_terminal (graph := setup.revealRelaxedGraph) left terminal⟩ :
          {config : setup.informationGraph.Config // config.cut.Terminal}) =
        ⟨rankedConfig (graph := setup.revealRelaxedGraph) right rightTerminal,
          rankedConfig_terminal (graph := setup.revealRelaxedGraph) right rightTerminal⟩ :=
      Subtype.ext (rankedConfig_congr (graph := setup.revealRelaxedGraph) same terminal
          rightTerminal)
    rw [outcome]
  · have rightTerminal : ¬ right.cut.Terminal := cut ▸ terminal
    rw [dite_eq_right terminal, dite_eq_right rightTerminal]

theorem concurrentPayoff_of_defaulted (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (config : setup.revealRelaxedGraph.Config)
    (defaulted : who ∈ config.defaulted) :
    setup.concurrentPayoff parameter utility excludedPayoff who config = excludedPayoff who := by
  unfold concurrentPayoff
  by_cases terminal : config.cut.Terminal
  · rw [dite_eq_left terminal]
    apply exclusionUtility_of_defaulted
    change who ∈ (rankedConfig (graph := setup.revealRelaxedGraph) config terminal).defaulted
    rw [defaulted_rankedConfig]
    exact defaulted
  · rw [dite_eq_right terminal]

theorem le_concurrentPayoff (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    (low : ∀ outcome, excludedPayoff who ≤ utility outcome who)
    (config : setup.revealRelaxedGraph.Config) :
    excludedPayoff who ≤ setup.concurrentPayoff parameter utility excludedPayoff who config := by
  unfold concurrentPayoff exclusionUtility
  split
  · split
    · exact le_rfl
    · exact low _
  · exact le_rfl

/-- The initial law of the concurrent graph: the setup draw, encoded as inputs. -/
abbrev concurrentInputs (setup : Setup (Player := Player) (L := L)) :
    PMF setup.revealRelaxedGraph.Inputs :=
  setup.initialLaw.map fun initial => setup.eventInputs initial

theorem concurrentInputs_support_finite (setup : Setup (Player := Player) (L := L))
    [setup.FiniteInitialLaw] : setup.concurrentInputs.support.Finite := by
  rw [PMF.support_map]
  exact setup.initialLaw_support_finite.image _

theorem concurrentRun_support_finite (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : setup.revealRelaxedGraph.BehavioralProfile)
    (scheduler : setup.revealRelaxedGraph.PublicScheduler) :
    (setup.concurrentInputs.bind
      (setup.revealRelaxedGraph.runPolicies scheduler profile)).support.Finite := by
  rw [PMF.support_bind]
  exact setup.concurrentInputs_support_finite.biUnion fun initial _ =>
    setup.revealRelaxedGraph.runPolicies_support_finite scheduler profile
      ((toInformationGraph_finiteActions setup.program finite).profileFiniteSupport profile) initial

/-- **Canonical identity.** Under canonical scheduling the concurrent graph's
expected payoff is the compiled canonical game's expected exclusion utility. -/
theorem expect_concurrentPayoff_canonical (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (profile :
      setup.informationGraph.BehavioralProfile) :
    expect (setup.concurrentInputs.bind (setup.revealRelaxedGraph.runPolicies
        setup.revealRelaxedGraph.canonicalScheduler profile))
        (setup.concurrentPayoff parameter utility excludedPayoff who) =
      expect (setup.canonicalEventGame.play profile) fun outcome =>
        exclusionUtility setup.program excludedPayoff utility
          (setup.eventParameterOutcome parameter outcome) who := by
  have actions := toInformationGraph_finiteActions setup.program finite
  let readout : setup.informationGraph.Config → ℝ := fun config =>
    if terminal : config.cut.Terminal then
      exclusionUtility setup.program excludedPayoff utility
        (setup.eventParameterOutcome parameter ⟨config, terminal⟩) who
    else 0
  have play : setup.canonicalEventGame.play profile = setup.concurrentInputs.bind
      (setup.informationGraph.terminalOutcomes setup.informationGraph.canonicalScheduler profile)
        := rfl
  rw [play, expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _
      (setup.concurrentRun_support_finite finite profile _)),
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _ (by
      rw [PMF.support_bind]
      exact setup.concurrentInputs_support_finite.biUnion fun initial _ => by
        have run := setup.informationGraph.runPolicies_support_finite
          setup.informationGraph.canonicalScheduler profile (actions.profileFiniteSupport profile)
          initial
        rw [← setup.informationGraph.terminalOutcomes_map_val, PMF.support_map] at run
        exact run.of_finite_image Subtype.val_injective.injOn))]
  apply expect_congr_on_support
  intro initial _
  have law := setup.revealRelaxedGraph.canonical_fromSequential_config_law profile initial
  rw [← law, expect_map]
  have outcomes : expect (setup.informationGraph.terminalOutcomes
    setup.informationGraph.canonicalScheduler
      profile initial) (fun outcome => exclusionUtility setup.program excludedPayoff utility
        (setup.eventParameterOutcome parameter outcome) who) =
      expect (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler profile
        initial)
        readout := by
    rw [← setup.informationGraph.terminalOutcomes_map_val, expect_map]
    apply expect_congr_on_support
    intro outcome _
    simp only [Function.comp_apply, readout, dite_eq_left outcome.2, Subtype.coe_eta]
  refine Eq.trans ?_ outcomes.symm
  change expect (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler
    profile initial)
      (setup.concurrentPayoff parameter utility excludedPayoff who ∘
        setup.revealRelaxedGraph.fromSequentialConfig) = _
  apply expect_congr_on_support
  intro config member
  have reach := setup.informationGraph.run_reachable initial _ config member
  have terminal := setup.informationGraph.runPolicies_terminal _ profile initial config member
  have viewTerminal : (setup.revealRelaxedGraph.fromSequentialConfig config).cut.Terminal :=
    terminal
  simp only [Function.comp_apply, concurrentPayoff, readout, dite_eq_left viewTerminal,
    dite_eq_left terminal]
  have recast := rankedConfig_fromSequentialConfig
    (graph := setup.revealRelaxedGraph) reach viewTerminal
  have outcome : (⟨rankedConfig (graph := setup.revealRelaxedGraph)
      (setup.revealRelaxedGraph.fromSequentialConfig config)
        viewTerminal, rankedConfig_terminal (graph := setup.revealRelaxedGraph) _ viewTerminal⟩ :
          {config : setup.informationGraph.Config // config.cut.Terminal}) = ⟨config, terminal⟩ :=
    Subtype.ext recast
  rw [outcome]

/-- Under canonical scheduling, normalization changes no play of the compiled game. -/
theorem canonicalEventGame_play_normalizeProfile (setup : Setup (Player := Player) (L := L))
    (profile : setup.informationGraph.BehavioralProfile) :
    setup.canonicalEventGame.play (setup.informationGraph.normalizeProfile profile) =
      setup.canonicalEventGame.play profile := by
  change setup.concurrentInputs.bind (setup.informationGraph.terminalOutcomes _ _) =
    setup.concurrentInputs.bind (setup.informationGraph.terminalOutcomes _ _)
  congr 1
  funext initial
  apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
  rw [EventGraph.terminalOutcomes_map_val, EventGraph.terminalOutcomes_map_val]
  exact runPolicies_canonical_normalizeProfile setup.informationGraph_total profile initial

/-- **Intended-game Nash under every schedule of concurrent reveals.** For a
well-formed setup with finite commitment payload types and an excluded payoff
below every utility, let a source profile disclose at every reveal and extend
an `ε`-Nash equilibrium of the intended game under the forfeiture interface.
On the compiled graph with independent reveals concurrent, its compiled
clients, normalized to ignore completion order, are an `ε`-Nash equilibrium
under every public scheduler, for the exclusion utility of the outcome read in
instruction order. -/
theorem concurrentReveal_intended_isεNash (setup : Setup (Player := Player) (L := L))
    [Finite Player] (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (low : ∀ outcome who, excludedPayoff who ≤ utility outcome who)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (scheduler : setup.revealRelaxedGraph.PublicScheduler) :
    IsεNash (setup.revealRelaxedGraph.gameForm setup.concurrentInputs scheduler)
      (fun outcome who => setup.concurrentPayoff parameter utility excludedPayoff who outcome.1) ε
      (setup.revealRelaxedGraph.normalizeProfile (compileEventProfile setup.program
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
          target))) := by
  let admission := CommitmentInterface.forfeiture setup.program
  let source := setup.decodeBehavioralProfile admission target
  let compiled : setup.informationGraph.BehavioralProfile := compileEventProfile setup.program
    source
  let exclusion := exclusionUtility setup.program excludedPayoff utility
  have actions := toInformationGraph_finiteActions setup.program finite
  -- The source chain: intended Nash, protocol Nash, source Nash, compiled canonical Nash.
  have protocolNash := (setup.intended_isεNash_preserved admission finite wellFormed parameter
    utility excludedPayoff (fun _ _ _ who => low _ who) intended target agrees ε equilibrium).1
  have sourceNash := (setup.parameterProtocol_isεNash_iff admission
    (fun _ policy => policy.admitted_forfeiture setup.program) parameter exclusion ε target).mp
      protocolNash
  have graphNash := (setup.parameterEventGame_approximate_nash_iff parameter finite
    setup.informationGraph.canonicalScheduler exclusion ε source).mpr sourceNash
  rw [IsεNash, isNash_iff] at graphNash
  have canonicalBound (who : Player) (policy : setup.informationGraph.BehavioralPolicy who) :
      expect (setup.canonicalEventGame.play
          (Profile.update (sig := setup.informationGraph.gameSignature) compiled who policy))
          (fun outcome => exclusion (setup.eventParameterOutcome parameter outcome) who) ≤
        expect (setup.canonicalEventGame.play compiled)
          (fun outcome => exclusion (setup.eventParameterOutcome parameter outcome) who) + ε := by
    have preference := graphNash who policy
    rwa [euPreferenceWithin_iff _ _ _ _ _
      (payoffIntegrable_of_finite_support _ _ (setup.eventGame_play_support_finite finite _ _))
      (payoffIntegrable_of_finite_support _ _ (setup.eventGame_play_support_finite finite _ _))]
      at preference
  -- The compiled clients open decisively and ignore observations at publications.
  have opens (who : Player) (event : setup.revealRelaxedGraph.EventId)
      (actor : setup.revealRelaxedGraph.actor? event = some who)
      (publication : (setup.revealRelaxedGraph.outputLayout event).IsPublication)
      (observation : setup.revealRelaxedGraph.PlayerObservation who)
      (active : who ∉ observation.defaulted) :
      compiled who event actor observation active =
        PMF.pure (EventField.openAction _ publication) :=
    compileEventPolicy_publication setup.program who (source who) (disclosing who) event actor
      publication observation active
  have oblivious : setup.revealRelaxedGraph.ObliviousAtPublications compiled :=
    fun who event actor publication left right leftActive rightActive => by
      rw [opens who event actor publication left leftActive,
        opens who event actor publication right rightActive]
  have canonicalConcurrent (who : Player) (profile : setup.informationGraph.BehavioralProfile) :
      expect (setup.concurrentInputs.bind (setup.revealRelaxedGraph.runPolicies
          setup.revealRelaxedGraph.canonicalScheduler
            (setup.revealRelaxedGraph.normalizeProfile profile)))
          (setup.concurrentPayoff parameter utility excludedPayoff who) =
        expect (setup.canonicalEventGame.play profile)
          (fun outcome => exclusion (setup.eventParameterOutcome parameter outcome) who) :=
    (setup.expect_concurrentPayoff_canonical finite parameter utility excludedPayoff who
      (setup.informationGraph.normalizeProfile profile)).trans
        (congrArg (fun law => expect law (fun outcome =>
          exclusion (setup.eventParameterOutcome parameter outcome) who))
          (setup.canonicalEventGame_play_normalizeProfile profile))
  exact (setup.informationGraph.relaxReveals_revealsOnlyConcurrent
    setup.informationGraph_total).isεNash_normalizeProfile actions compiled oblivious
    (fun who => opensDecisively_of_opens who _ fun _ event actor publication active =>
      opens who event actor publication _ _)
    (fun who => setup.concurrentPayoff parameter utility excludedPayoff who)
    (fun who => setup.concurrentPayoff_factors parameter utility excludedPayoff who)
    excludedPayoff
    (fun who => setup.le_concurrentPayoff parameter utility excludedPayoff who
      (fun outcome => low outcome who))
    (fun who => setup.concurrentPayoff_of_defaulted parameter utility excludedPayoff who)
    setup.concurrentInputs setup.concurrentInputs_support_finite ε
    (fun who policy => by
      rw [canonicalConcurrent who, canonicalConcurrent who]
      exact canonicalBound who policy)
    scheduler

/-- The terminal source configuration of a concurrent play, read in instruction order. -/
def concurrentReadout (setup : Setup (Player := Player) (L := L))
    (outcome : setup.revealRelaxedGraph.gameSignature.Outcome) :
    Config Player L setup.program.terminalCtx :=
  terminalConfig setup.program
    ⟨rankedConfig (graph := setup.revealRelaxedGraph) outcome.1 outcome.2, rankedConfig_terminal
        (graph := setup.revealRelaxedGraph) outcome.1 outcome.2⟩

/-- The source-order readout and payoffs of a concurrent configuration. -/
def concurrentObservation (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (config : setup.revealRelaxedGraph.Config) :
    Option (Config Player L setup.program.terminalCtx) × (Player → ℝ) :=
  (if terminal : config.cut.Terminal then
      some (terminalConfig setup.program
        ⟨rankedConfig (graph := setup.revealRelaxedGraph) config terminal, rankedConfig_terminal
            (graph := setup.revealRelaxedGraph) config terminal⟩)
    else none,
    fun who => setup.concurrentPayoff parameter utility excludedPayoff who config)

private theorem concurrentObservation_factors (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (left right : setup.revealRelaxedGraph.Config)
    (same : runKey left = runKey right) :
    setup.concurrentObservation parameter utility excludedPayoff left =
      setup.concurrentObservation parameter utility excludedPayoff right := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  unfold concurrentObservation
  refine Prod.ext ?_ (funext fun who =>
    setup.concurrentPayoff_factors parameter utility excludedPayoff who left right same)
  by_cases terminal : left.cut.Terminal
  · have rightTerminal : right.cut.Terminal := cut ▸ terminal
    simp only [dite_eq_left terminal, dite_eq_left rightTerminal]
    have outcome : (⟨rankedConfig (graph := setup.revealRelaxedGraph) left terminal,
        rankedConfig_terminal (graph := setup.revealRelaxedGraph) left terminal⟩ :
          {config : setup.informationGraph.Config // config.cut.Terminal}) =
        ⟨rankedConfig (graph := setup.revealRelaxedGraph) right rightTerminal,
          rankedConfig_terminal (graph := setup.revealRelaxedGraph) right rightTerminal⟩ :=
      Subtype.ext (rankedConfig_congr (graph := setup.revealRelaxedGraph) same terminal
          rightTerminal)
    rw [outcome]
  · have rightTerminal : ¬ right.cut.Terminal := cut ▸ terminal
    simp only [dite_eq_right terminal, dite_eq_right rightTerminal]

private theorem canonical_concurrentObservation_law (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (profile : setup.informationGraph.BehavioralProfile) :
    (setup.concurrentInputs.bind (setup.revealRelaxedGraph.runPolicies
        setup.revealRelaxedGraph.canonicalScheduler
          (setup.revealRelaxedGraph.normalizeProfile profile))).map
        (setup.concurrentObservation parameter utility excludedPayoff) =
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
  have play : setup.canonicalEventGame.play profile = setup.concurrentInputs.bind
      (setup.informationGraph.terminalOutcomes setup.informationGraph.canonicalScheduler profile)
        := rfl
  rw [play, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  have law := setup.revealRelaxedGraph.canonical_fromSequential_config_law
    (setup.revealRelaxedGraph.normalizeProfile profile) initial
  have normalized := runPolicies_canonical_normalizeProfile setup.informationGraph_total profile
    initial
  have outcomes : (setup.informationGraph.terminalOutcomes setup.informationGraph.canonicalScheduler
      profile initial).map (fun outcome => (some (terminalConfig setup.program outcome),
        fun who => exclusionUtility setup.program excludedPayoff utility
          (setup.eventParameterOutcome parameter outcome) who)) =
      (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler profile
        initial).map
        readout := by
    rw [← setup.informationGraph.terminalOutcomes_map_val, PMF.map_comp]
    apply map_congr_on_support _
    intro outcome _
    simp only [Function.comp_apply, readout, dite_eq_left outcome.2, Subtype.coe_eta]
  refine Eq.trans ?_ outcomes.symm
  rw [← law, PMF.map_comp]
  change (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler
    (setup.informationGraph.normalizeProfile profile) initial).map _ = _
  rw [normalized]
  apply map_congr_on_support _
  intro config member
  have reach := setup.informationGraph.run_reachable initial _ config member
  have terminal := setup.informationGraph.runPolicies_terminal _ profile initial config member
  have viewTerminal : (setup.revealRelaxedGraph.fromSequentialConfig config).cut.Terminal :=
    terminal
  have recast := rankedConfig_fromSequentialConfig
    (graph := setup.revealRelaxedGraph) reach viewTerminal
  have outcome : (⟨rankedConfig (graph := setup.revealRelaxedGraph)
      (setup.revealRelaxedGraph.fromSequentialConfig config)
        viewTerminal, rankedConfig_terminal (graph := setup.revealRelaxedGraph) _ viewTerminal⟩ :
          {config : setup.informationGraph.Config // config.cut.Terminal}) = ⟨config, terminal⟩ :=
    Subtype.ext recast
  simp only [Function.comp_apply, concurrentObservation, concurrentPayoff, readout,
    dite_eq_left viewTerminal, dite_eq_left terminal, outcome]

/-- **Intended law under every schedule of concurrent reveals.** Under the
hypotheses of `concurrentReveal_intended_isεNash`, the order-blind compiled
clients have, under every public scheduler, the intended joint law of terminal
configuration, read in instruction order, and payoff vector. -/
theorem concurrentReveal_intended_law (setup : Setup (Player := Player) (L := L))
    [Finite Player] (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (low : ∀ outcome who, excludedPayoff who ≤ utility outcome who)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (scheduler : setup.revealRelaxedGraph.PublicScheduler) :
    ((setup.revealRelaxedGraph.gameForm setup.concurrentInputs scheduler).play
        (setup.revealRelaxedGraph.normalizeProfile (compileEventProfile setup.program
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
            target)))).map (fun outcome => (some (setup.concurrentReadout outcome),
          fun who => setup.concurrentPayoff parameter utility excludedPayoff who outcome.1)) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state, fun who =>
          (setup.protocolReadout final.state).elim 0
            (fun state => utility (setup.parameterOutcome parameter state) who))) := by
  let admission := CommitmentInterface.forfeiture setup.program
  let source := setup.decodeBehavioralProfile admission target
  let compiled : setup.informationGraph.BehavioralProfile := compileEventProfile setup.program
    source
  let exclusion := exclusionUtility setup.program excludedPayoff utility
  have preserved := setup.intended_isεNash_preserved admission finite wellFormed parameter
    utility excludedPayoff (fun _ _ _ who => low _ who) intended target agrees ε equilibrium
  have opens (who : Player) (event : setup.revealRelaxedGraph.EventId)
      (actor : setup.revealRelaxedGraph.actor? event = some who)
      (publication : (setup.revealRelaxedGraph.outputLayout event).IsPublication)
      (observation : setup.revealRelaxedGraph.PlayerObservation who)
      (active : who ∉ observation.defaulted) :
      compiled who event actor observation active =
        PMF.pure (EventField.openAction _ publication) :=
    compileEventPolicy_publication setup.program who (source who) (disclosing who) event actor
      publication observation active
  have oblivious : setup.revealRelaxedGraph.ObliviousAtPublications compiled :=
    fun who event actor publication left right leftActive rightActive => by
      rw [opens who event actor publication left leftActive,
        opens who event actor publication right rightActive]
  have only := setup.informationGraph.relaxReveals_revealsOnlyConcurrent
    setup.informationGraph_total
  -- Play to runs.
  have mapped : ((setup.revealRelaxedGraph.gameForm setup.concurrentInputs scheduler).play
      (setup.revealRelaxedGraph.normalizeProfile compiled)).map Subtype.val =
        setup.concurrentInputs.bind (setup.revealRelaxedGraph.runPolicies scheduler
          (setup.revealRelaxedGraph.normalizeProfile compiled)) := by
    change (setup.concurrentInputs.bind _).map Subtype.val = _
    rw [PMF.map_bind]
    simp only [EventGraph.terminalOutcomes_map_val]
  have observed : (fun outcome : setup.revealRelaxedGraph.gameSignature.Outcome =>
      (some (setup.concurrentReadout outcome),
        fun who => setup.concurrentPayoff parameter utility excludedPayoff who outcome.1)) =
      setup.concurrentObservation parameter utility excludedPayoff ∘ Subtype.val := by
    funext outcome
    simp only [Function.comp_apply, concurrentObservation, dite_eq_left outcome.2,
      concurrentReadout]
  change PMF.map _ ((setup.revealRelaxedGraph.gameForm setup.concurrentInputs scheduler).play
    (setup.revealRelaxedGraph.normalizeProfile compiled)) = _
  rw [observed, ← PMF.map_comp, mapped,
    only.runPolicies_map_eq_canonical compiled oblivious scheduler setup.concurrentInputs _
      (setup.concurrentObservation_factors parameter utility excludedPayoff),
    setup.canonical_concurrentObservation_law parameter utility excludedPayoff compiled]
  -- The compiled canonical law is the source law.
  have sourceLaw := canonical_setup_law setup source
  have throughSource : (setup.canonicalEventGame.play compiled).map (fun outcome =>
      (some (terminalConfig setup.program outcome), fun who =>
        exclusion (setup.eventParameterOutcome parameter outcome) who)) =
      (setup.run source).map (fun terminal => (some terminal, fun who =>
        exclusion (setup.parameterOutcome parameter terminal) who)) := by
    rw [← sourceLaw, PMF.map_comp]
    rfl
  rw [throughSource]
  -- The source law is the protocol readout law.
  have protocolLaw := (setup.protocol_readout_law admission).1 target
  have viaSome : (setup.run source).map (fun terminal => (some terminal, fun who =>
      exclusion (setup.parameterOutcome parameter terminal) who)) =
      ((setup.run source).map some).map (fun readout => (readout, fun who =>
        readout.elim 0 (fun terminal => exclusion (setup.parameterOutcome parameter terminal)
          who))) := by
    rw [PMF.map_comp]
    rfl
  rw [viaSome, ← protocolLaw, PMF.map_comp]
  exact preserved.2.2

end Vegas.SourceProgram.Setup
