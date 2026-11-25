module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealServiceHonestDistribution
public import Vegas.Game.RevealServiceReference
public import Vegas.Compile.EventGraphCanonical
public import Vegas.EventGraph.SequentialNormalization

@[expose] public section

/-! # The source outcome law of honest clients with concurrent reveals

On the service graph with independent reveals concurrent, the first-turn
clients of the order-blind reference of a disclosing source profile have, under
every public scheduler and the asynchronous service contract, the source law of
the parameter, public values and public defaults. The reference's outcome law
from the initial configurations is that source law, because its canonical run
is the sequential compiled run read in instruction order.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The instruction-order source configuration of a reachable terminal
sequential run, viewed on the concurrent-reveal graph, is its source
configuration. -/
theorem concurrentRankedRead_fromSequential (setup : Setup (Player := Player) (L := L))
    {inputs : setup.informationGraph.Inputs} {config : setup.informationGraph.Config}
    (reach : EventGraph.Config.Reachable inputs config) (terminal : config.cut.Terminal) :
    concurrentRankedRead setup (setup.revealRelaxedGraph.fromSequentialConfig config) =
      some (terminalConfig setup.program ⟨config, terminal⟩) := by
  have viewTerminal : (setup.revealRelaxedGraph.fromSequentialConfig config).cut.Terminal :=
    terminal
  have recast := rankedConfig_fromSequentialConfig
    (graph := setup.revealRelaxedGraph) reach viewTerminal
  unfold concurrentRankedRead
  rw [ite_eq_left viewTerminal]
  have viaRanked : decodeConfig? setup.program setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) [] (outputEmbedding setup.program)
      (setup.revealRelaxedGraph.fromSequentialConfig config).store
      (EventGraph.rankedHistory (graph := setup.revealRelaxedGraph)
        (setup.revealRelaxedGraph.fromSequentialConfig config)) =
    decodeConfig? setup.program setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) [] (outputEmbedding setup.program)
      (rankedConfig _ viewTerminal).store (rankedConfig _ viewTerminal).history := by
    congr 1
    funext field
    cases field <;> rfl
  rw [viaRanked, recast]
  exact decodeConfig?_terminal setup.program ⟨config, terminal⟩

/-- The instruction-order outcome of a reachable terminal sequential run, viewed
on the concurrent-reveal graph, is the outcome of its source configuration. -/
theorem concurrentOutcome_fromSequential (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    {inputs : setup.informationGraph.Inputs} {config : setup.informationGraph.Config}
    (reach : EventGraph.Config.Reachable inputs config) (terminal : config.cut.Terminal) :
    concurrentOutcome setup parameter
        (setup.revealRelaxedGraph.fromSequentialConfig config) =
      some (setup.parameterOutcome parameter (terminalConfig setup.program
        ⟨config, terminal⟩)) := by
  unfold concurrentOutcome
  rw [concurrentRankedRead_fromSequential setup reach terminal, Option.map_some]

/-- The typed state and public defaults of the source configuration read in
instruction order. -/
def concurrentStateRead (setup : Setup (Player := Player) (L := L)) {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome)
    (config : setup.revealRelaxedGraph.Config) : Option Outcome :=
  (concurrentRankedRead setup config).map (fun final => read (final.state, final.defaults))

/-- The typed state and public defaults ignore the decisions of defaulted
players. -/
theorem concurrentStateRead_erase (setup : Setup (Player := Player) (L := L)) {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome)
    (config : setup.revealRelaxedGraph.Config) :
    concurrentStateRead setup read config.erase = concurrentStateRead setup read config := by
  have defaultsEq : Vegas.EventCompletion.defaults (EventGraph.rankedHistory config.erase) =
      Vegas.EventCompletion.defaults (EventGraph.rankedHistory config) := by
    rw [rankedHistory_erase]
    unfold Vegas.EventCompletion.defaults
    simp only [List.map_map, Function.comp_def, eraseCompletion_defaultEvent]
  unfold concurrentStateRead concurrentRankedRead
  change (if config.cut.Terminal then _ else none).map _ =
    (if config.cut.Terminal then _ else none).map _
  split
  · unfold Vegas.decodeConfig?
    rw [Option.map_map, Option.map_map]
    change Option.map _ (Vegas.decodeState? _ config.store) =
      Option.map _ (Vegas.decodeState? _ config.store)
    congr 1
    funext state
    simp only [Function.comp_apply, defaultsEq]
  · rfl

/-- A readout through the instruction-order reader of a reachable terminal
sequential run's view is the readout of its source configuration: the canonical
law of the order-blind reference from the initial configurations is the source
law of that readout. -/
private theorem concurrentReference_initial_distribution (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program) {Outcome : Type*}
    (read : setup.revealRelaxedGraph.Config → Outcome)
    (observe : Config Player L setup.program.terminalCtx → Outcome)
    (readSequential : ∀ {inputs : setup.informationGraph.Inputs} {config :
      setup.informationGraph.Config},
      EventGraph.Config.Reachable inputs config → (terminal : config.cut.Terminal) →
      read (setup.revealRelaxedGraph.fromSequentialConfig config) =
        observe (terminalConfig setup.program ⟨config, terminal⟩)) :
    (serviceInitialDistribution setup setup.revealDependencies).bind (fun state =>
        outcomeDistribution (concurrentReference setup source) read state.config) =
      (setup.run source).map observe := by
  let compiled : setup.informationGraph.BehavioralProfile := compileEventProfile setup.program
    source
  have sourceDistribution := canonical_setup_distribution setup source
  rw [← sourceDistribution, PMF.map_comp]
  change _ = ((setup.initialDistribution.map fun initial => setup.eventInputs initial).bind
    (setup.informationGraph.terminalOutcomes setup.informationGraph.canonicalScheduler
      compiled)).map _
  rw [serviceInitialDistribution, PMF.bind_map, PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro initial _
  let inputs := setup.eventInputs initial
  have law := setup.revealRelaxedGraph.canonical_fromSequential_config_distribution
    (setup.revealRelaxedGraph.normalizeProfile compiled) inputs
  have normalized := runPolicies_canonical_normalizeProfile setup.informationGraph_total compiled
    inputs
  change (setup.revealRelaxedGraph.runPolicies setup.revealRelaxedGraph.canonicalScheduler
    (setup.revealRelaxedGraph.normalizeProfile compiled) inputs).map _ = _
  rw [← law, PMF.map_comp]
  change (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler
    (setup.informationGraph.normalizeProfile compiled) inputs).map _ = _
  rw [normalized, ← setup.informationGraph.terminalOutcomes_map_val, PMF.map_comp]
  change _ = PMF.map _ (setup.informationGraph.terminalOutcomes
    setup.informationGraph.canonicalScheduler
    compiled inputs)
  apply map_congr_on_support _
  intro outcome member
  have reach := setup.informationGraph.run_reachable inputs _ outcome.1
    ((setup.informationGraph.terminalOutcomes_map_val _ compiled inputs) ▸
      (PMF.mem_support_map_iff _ _ _).mpr ⟨outcome, member, rfl⟩)
  exact readSequential reach outcome.2

/-- **The reference's initial outcome law is the source law.** -/
theorem concurrentReference_initial_outcomeDistribution (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program) {Parameter : Type}
    (parameter : State L setup.context → Parameter) :
    (serviceInitialDistribution setup setup.revealDependencies).bind (fun state =>
        outcomeDistribution (concurrentReference setup source) (concurrentOutcome setup parameter)
          state.config) =
      (setup.run source).map (fun final => some (setup.parameterOutcome parameter final)) :=
  concurrentReference_initial_distribution setup source (concurrentOutcome setup parameter) _
    (fun reach terminal => concurrentOutcome_fromSequential setup parameter reach terminal)

/-- **The reference's initial state law is the source law.** -/
theorem concurrentReference_initial_stateDistribution (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program) {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    (serviceInitialDistribution setup setup.revealDependencies).bind (fun state =>
        outcomeDistribution (concurrentReference setup source) (concurrentStateRead setup read)
          state.config) =
      (setup.run source).map (fun final => some (read (final.state, final.defaults))) :=
  concurrentReference_initial_distribution setup source (concurrentStateRead setup read) _
    (fun reach terminal => by
      unfold concurrentStateRead
      rw [concurrentRankedRead_fromSequential setup reach terminal, Option.map_some])


/-- **Honest clients have the source outcome law under every public scheduler.**
Under the asynchronous service contract, on the service graph with independent
reveals concurrent, the first-turn clients of the order-blind reference of a
disclosing source profile have, read in instruction order, the source law of
the parameter, public values and public defaults. -/
theorem concurrentClients_outcome_distribution (setup : Setup (Player := Player) (L := L))
    (duration : setup.revealRelaxedGraph.EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket setup.revealRelaxedGraph))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup setup.revealDependencies duration leaks).Scheduler}
    {delay bound : setup.revealRelaxedGraph.EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup setup.revealDependencies duration) leaks
      (serviceInitialDistribution setup setup.revealDependencies) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup setup.revealDependencies duration) delay bound)
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who))
    {Parameter : Type} (parameter : State L setup.context → Parameter) :
    ((serviceApplication setup setup.revealDependencies duration leaks).roundsFrom
        (serviceInitialDistribution setup setup.revealDependencies) scheduler
        (turnPolicy (serviceTimeouts setup setup.revealDependencies duration) leaks bound turns
          (firstTurnTiming setup turns setup.revealDependencies) (concurrentReference setup source))
        horizon).map (fun final =>
          (serviceRankedReadout setup setup.revealDependencies duration leaks
            ((serviceApplication setup setup.revealDependencies duration leaks).finished final)).map
            (setup.parameterOutcome parameter)) =
      (setup.run source).map (fun final => some (setup.parameterOutcome parameter final)) := by
  have keyed (left right : setup.revealRelaxedGraph.Config)
      (same : runKey left = runKey right) :
      concurrentOutcome setup parameter left = concurrentOutcome setup parameter right := by
    unfold concurrentOutcome
    rw [concurrentRankedRead_congr setup same]
  have law := honest_roundsFrom_outcomeDistribution (duration := duration) (leaks := leaks)
    (turns := turns) contract timely
    (setup.informationGraph.relaxReveals_revealsOnlyConcurrent setup.informationGraph_total)
    (fun _ notPublication => setup.informationGraph.relaxReveals_leading
      setup.informationGraph_total notPublication)
    (concurrentReference setup source)
      (concurrentReference_readyIndependent setup source disclosing)
    (concurrentReference_opensPublications setup source disclosing)
    (concurrentOutcome setup parameter) keyed (concurrentOutcome_erase setup parameter)
  exact law.trans (concurrentReference_initial_outcomeDistribution setup source parameter)


/-- **Honest clients have the source state law under every public scheduler.**
Under the asynchronous service contract, on the service graph with independent
reveals concurrent, the first-turn clients of the order-blind reference of a
disclosing source profile have, read in instruction order, the source law of
every observation of the typed terminal state and public default history. -/
theorem concurrentClients_state_distribution (setup : Setup (Player := Player) (L := L))
    (duration : setup.revealRelaxedGraph.EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket setup.revealRelaxedGraph))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup setup.revealDependencies duration leaks).Scheduler}
    {delay bound : setup.revealRelaxedGraph.EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup setup.revealDependencies duration) leaks
      (serviceInitialDistribution setup setup.revealDependencies) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup setup.revealDependencies duration) delay bound)
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who))
    {Outcome : Type*} (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    ((serviceApplication setup setup.revealDependencies duration leaks).roundsFrom
        (serviceInitialDistribution setup setup.revealDependencies) scheduler
        (turnPolicy (serviceTimeouts setup setup.revealDependencies duration) leaks bound turns
          (firstTurnTiming setup turns setup.revealDependencies) (concurrentReference setup source))
        horizon).map (fun final =>
          (serviceRankedReadout setup setup.revealDependencies duration leaks
            ((serviceApplication setup setup.revealDependencies duration leaks).finished final)).map
            (fun config => read (config.state, config.defaults))) =
      (setup.run source).map (fun final => some (read (final.state, final.defaults))) := by
  have keyed (left right : setup.revealRelaxedGraph.Config)
      (same : runKey left = runKey right) :
      concurrentStateRead setup read left = concurrentStateRead setup read right := by
    unfold concurrentStateRead
    rw [concurrentRankedRead_congr setup same]
  have law := honest_roundsFrom_outcomeDistribution (duration := duration) (leaks := leaks)
    (turns := turns) contract timely
    (setup.informationGraph.relaxReveals_revealsOnlyConcurrent setup.informationGraph_total)
    (fun _ notPublication => setup.informationGraph.relaxReveals_leading
      setup.informationGraph_total notPublication)
    (concurrentReference setup source)
      (concurrentReference_readyIndependent setup source disclosing)
    (concurrentReference_opensPublications setup source disclosing)
    (concurrentStateRead setup read) keyed (concurrentStateRead_erase setup read)
  exact law.trans (concurrentReference_initial_stateDistribution setup source read)

end Vegas
