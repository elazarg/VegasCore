module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceAsyncStep
public import Vegas.Game.SourceServiceContinuation
public import Vegas.Compile.EventGraphCanonical
public import Vegas.Source.DisclosureBehavioral

@[expose] public section

/-! # Ready sites and the initialized source law

A decision on the sequentialized graph is located by its ready site: the event
whose phase it lies in, that event's readiness, and that it is the only ready
event (`Vegas.ReadySite`). No plan position, roster or calendar is involved.

The source continuation from the initial boundary, averaged over the native
prior, is the source law (`Vegas.initialDistribution_bind_sourceContinuation`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The position-free datum of a decision: the event whose phase the execution
is in, that event's readiness, and that it is the only ready event. -/
structure ReadySite (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (execution : (application setup (Vegas.timeouts setup) leaks).Execution) where
  event : setup.informationGraph.EventId
  ready : execution.application.config.cut.Ready event
  sole : execution.application.publicView.SoleReady event

/-! ## The initialized law -/

section Initialized

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))

/-- The source continuation from the initial boundary, averaged over the
native prior, is the source law. -/
theorem initialDistribution_bind_sourceContinuation (profile : BehavioralProfile setup.program) :
    (initialDistribution setup).bind (fun state => sourceContinuation setup profile 0 state.config)
      =
      (setup.run profile).map some := by
  rw [initialDistribution, serviceInitialDistribution, PMF.bind_map, Setup.run, PMF.map_bind]
  congr 1
  funext initial
  change sourceContinuation setup profile 0
    (EventGraph.Config.initial (graph := setup.informationGraph) (setup.eventInputs initial)) = _
  simp only [sourceContinuation, serviceSourcePrefix?_initial, Setup.continuationDistribution,
    ProtocolState.continuationDistribution_entry]
  rfl

variable {setup leaks} [Fintype Player]

end Initialized

/-- The complete clients preserve every observation of the original source's
typed state and public defaults once their first-turn source law holds. -/
theorem sourceServiceClientPolicy_source_observation_distribution_eq_of_firstTurn
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    {horizon turns : Nat} {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {bound : (serviceGraph setup deps).EventId → Nat}
    (original : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceAgreement setup deps duration leaks horizon scheduler bound turns
      (normalizeDisclosureProfile setup.program original))
    {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialDistribution setup deps)
      scheduler (serviceClientPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (normalizeDisclosureProfile setup.program original))
      horizon).map (fun execution =>
        (serviceSourceReadout setup deps duration leaks
          ((serviceApplication setup deps duration leaks).finished execution)).map
          (fun final => read (final.state, final.defaults))) =
      (setup.run original).map (fun final => some (read (final.state, final.defaults))) := by
  rw [sourceServiceClientPolicy_roundsFrom]
  have projected := congrArg
    (PMF.map (Option.map (fun final : Config Player L setup.program.terminalCtx =>
      read (final.state, final.defaults)))) terminal
  have normalized := congrArg (PMF.map (fun output => some (read output)))
    (setup.run_normalizeDisclosures_eq original)
  simp only [PMF.map_comp, Function.comp_def, Option.map_some]
    at projected normalized
  exact projected.trans normalized

variable (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts setup.informationGraph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))

/-- Project a full ledger-to-graph configuration law through the typed terminal decoder.
The ledger clients and the reference graph profile can be arbitrary. -/
theorem sourceReadout_distribution_of_config_distribution
    {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
    {players : Player → (application setup timeouts leaks).Policy}
    (reference : setup.informationGraph.BehavioralProfile)
    (law : ((application setup timeouts leaks).roundsFrom (initialDistribution setup) scheduler
      players
      horizon).map (fun final => final.application.config) =
        ((setup.informationGraph.canonicalGame (setup.initialDistribution.map
          setup.eventInputs)).play
          reference).map Subtype.val) :
    ((application setup timeouts leaks).roundsFrom (initialDistribution setup) scheduler players
      horizon).map
        (fun final => sourceReadout setup timeouts leaks
          ((application setup timeouts leaks).finished final)) =
      ((setup.informationGraph.canonicalGame (setup.initialDistribution.map setup.eventInputs)).play
        reference).map (fun final => some (terminalConfig setup.program final)) := by
  let read := fun config : setup.informationGraph.Config => decodeConfig? setup.program
    setup.program (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
    config.history
  have native (final : (application setup timeouts leaks).Execution) :
      sourceReadout setup timeouts leaks ((application setup timeouts leaks).finished final) =
        read final.application.config := by
    change serviceSourceReadout setup setup.informationDependencies timeouts.duration leaks (some
      ⟨0, none, final⟩) = _
    rw [serviceSourceReadout_eq_decode]
  have mapped := congrArg (PMF.map read) law
  simp only [PMF.map_comp, Function.comp_def] at mapped
  refine (map_congr_on_support _ fun final _ => native final).trans (mapped.trans ?_)
  let graphLaw := (setup.informationGraph.canonicalGame (setup.initialDistribution.map
    setup.eventInputs)).play reference
  exact map_congr_on_support graphLaw fun final _ => decodeConfig?_terminal setup.program final

end Vegas
