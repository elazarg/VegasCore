module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.CompiledProfileRealizability
public import Vegas.Game.SourceServiceFirstTurnOpportunity
public import Vegas.Game.SourceServiceTurnSubmissions
public import Vegas.Game.SourceServiceCanonicalAcceptance
public import Vegas.Pending.FirstTurnClientSimulation
public import Vegas.Game.SourceServiceSiteBridge
public import Vegas.Compile.EventGraphCanonical
public import Interaction.ReactiveMixtureRounds

@[expose] public section

/-! # Source compilation through first-turn graph simulation

Authentic source profiles compile to realizable graph profiles. Their physical clients therefore
have the graph's full configuration law. Decoding that law and applying source-to-graph correctness
recovers the source outcome distribution.
-/

noncomputable section

namespace Vegas

section Compilation

open SourceProgram EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}

/-- Fixing one owner's first source choice preserves its full canonical
continuation against arbitrary other players, including automatic completion. -/
theorem serviceReference_fixedAction_continuation
    (timeouts : EventTimeouts (serviceGraph setup deps))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {horizon turns : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (delay bound : (serviceGraph setup deps).EventId → Nat)
    (client : (serviceGraph setup deps).BehavioralProfile) {Result : Type*} (continuation :
      (serviceGraph setup deps).Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State (serviceGraph setup deps),
      continuation state.drain.config = continuation state.config)
    (contract : AsyncContract timeouts leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner) (solitary :
      (serviceGraph setup deps).Solitary event)
    (background : Player → ((reactiveApplication timeouts) leaks).Policy)
    (follows : background owner = turnPolicy timeouts leaks
      bound turns (firstTurnTiming setup turns deps) client owner)
    (action : (serviceGraph setup deps).Action event)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (supported : execution ∈ (((reactiveApplication timeouts) leaks).roundsFrom
      (serviceInitialDistribution setup deps) scheduler background
        execution.environmentRecall.length).support)
    (untouched : Untouched setup leaks event execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (effective : EffectiveAction execution.application.config event action) :
    let players := turnPolicy timeouts leaks bound turns
      (firstTurnTiming setup turns deps) client
    let member := fun past view =>
      if turnIndex timeouts leaks owner event past view = some 0 then
        fixedOpportunity timeouts leaks bound owner event action past view
      else players owner past view
    ((((reactiveApplication timeouts) leaks).runUntilHorizon scheduler
        (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        continuation stopped.application.config) =
      (execution.application.config.step event ready action).bind
        fun after => continuation after := by
  rw [serviceInitialDistribution_eq_inputs setup] at contract supported
  exact EventGraphRuntime.firstTurn_fixedAction_continuation timeouts leaks scheduler delay bound
    client continuation drained contract timely owner event owned solitary background follows action
    execution ready supported untouched bounded effective

/-- An honest owner's first callback draws its fixed source action before
stopped native play, with arbitrary other player policies. -/
theorem sourceService_firstTurn_mixture (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (bound : setup.informationGraph.EventId → Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : setup.informationGraph.EventId)
    (owned : setup.informationGraph.actor? event = some owner)
    (background : Player → (application setup timeouts leaks).Policy)
    (follows : background owner = serviceTurnPolicy setup setup.informationDependencies
      timeouts.duration leaks
      bound turns (firstTurnTiming setup turns) profile owner)
    (execution : (application setup timeouts leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      background event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (law : PMF (setup.informationGraph.Action event))
    (callback : ∀ current : (application setup timeouts leaks).Execution,
      current.application.config = execution.application.config →
      sourceServiceCanonicalPolicy setup timeouts leaks profile owner (current.logs owner)
          (current.observe (application setup timeouts leaks) owner) =
        law.map (fun action => (canonicalServiceDecision timeouts) leaks owner (current.logs owner)
          (current.observe (application setup timeouts leaks) owner) event action)) :
    let players := serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks
      bound turns
      (firstTurnTiming setup turns) profile
    ((application setup timeouts leaks).runUntilHorizon scheduler background
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
      law.bind (fun action => (application setup timeouts leaks).runUntilHorizon scheduler
        (Function.update background owner (fun past view =>
          if turnIndex timeouts leaks owner event
            past view = some 0
          then fixedOpportunity timeouts leaks bound owner event action past view
          else players owner past view))
        (fun final => event ∈ final.application.config.cut.completed) horizon execution) :=
  firstTurn_mixture timeouts leaks scheduler bound (compileEventProfile setup.program profile)
    owner event owned background follows execution
    (fun _ other => setup.informationGraph.sequentialize_solitary event _ other
      (boundary.ordered.ready event.isLt))
    boundary.supported (boundary.untouched event le_rfl owner) bounded law
    (fun current same _ => callback current same)

/-- Fixing one owner's first source choice preserves its full canonical
continuation against arbitrary other players, including automatic completion. -/
theorem sourceService_fixedAction_continuation
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat)
    (source : BehavioralProfile setup.program) (reference :
      setup.informationGraph.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound)
    (owner : Player) (event : setup.informationGraph.EventId)
    (owned : setup.informationGraph.actor? event = some owner)
    (background : Player → (application setup timeouts leaks).Policy)
    (follows : background owner = serviceTurnPolicy setup setup.informationDependencies
      timeouts.duration leaks
      bound turns (firstTurnTiming setup turns) source owner)
    (action : setup.informationGraph.Action event)
    (execution : (application setup timeouts leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      background event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (effective : EffectiveAction execution.application.config event action) :
    let players := serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks
      bound turns
      (firstTurnTiming setup turns) source
    let member := fun past view =>
      if turnIndex timeouts leaks owner event past
        view = some 0 then
        fixedOpportunity timeouts leaks bound owner event action past view
      else players owner past view
    (((application setup timeouts leaks).runUntilHorizon scheduler
        (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        setup.informationGraph.runPlan (setup.informationGraph.policyPlan reference
          setup.informationGraph.canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event (boundary.ordered.ready event.isLt) action).bind
        fun after => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan reference setup.informationGraph.canonicalScheduler)
            after.remaining
            after :=
  serviceReference_fixedAction_continuation timeouts leaks scheduler delay bound
    (compileEventProfile setup.program source)
    (fun config => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan reference setup.informationGraph.canonicalScheduler)
        config.remaining config)
    (fun state => (EventGraphRuntime.State.drain_runPlan_canonical setup.informationGraph reference
      state).symm) contract timely owner event owned (setup.informationGraph.sequentialize_solitary
        event)
    background follows action execution (boundary.ordered.ready event.isLt) boundary.supported
    (boundary.untouched event le_rfl) bounded effective

/-- First-turn clients of a profile with authentic disclosures have exactly the terminal
configuration distribution of the canonical compiled graph under the asynchronous service contract
and its reaction and inclusion bounds. -/
theorem firstTurnGraphDistribution_of_async
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat)
    (source : BehavioralProfile setup.program)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound)
    (authentic : ∀ who, (source who).AuthenticDisclosures setup.program) :
    ((application setup timeouts leaks).roundsFrom (initialDistribution setup) scheduler
      (serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) source) horizon).map
        (fun execution => execution.application.config) =
    ((setup.informationGraph.canonicalGame (setup.initialDistribution.map setup.eventInputs)).play
      (compileEventProfile setup.program source)).map Subtype.val := by
  have initEq := serviceInitialDistribution_eq_inputs setup (deps := setup.informationDependencies)
  unfold initialDistribution at contract ⊢
  rw [initEq] at contract ⊢
  exact EventGraphRuntime.firstTurn_config_distribution timeouts leaks scheduler delay bound
    (setup.initialDistribution.map setup.eventInputs) (compileEventProfile setup.program source)
      contract
    timely (compileEventProfile_realizable authentic)

/-- First-turn source clients preserve the full source configuration under the
asynchronous service contract and its reaction/inclusion timing budget. -/
theorem FirstTurnSourceMatches_of_async
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat)
    (source : BehavioralProfile setup.program)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound)
    (authentic : ∀ who, (source who).AuthenticDisclosures setup.program) :
    FirstTurnSourceAgreement setup setup.informationDependencies timeouts.duration leaks horizon
      scheduler bound turns
      source := by
  have raw := firstTurnGraphDistribution_of_async (turns := turns) timeouts leaks scheduler delay
    bound
    source contract timely authentic
  have graph := sourceReadout_distribution_of_config_distribution setup timeouts leaks _ raw
  have compiled := congrArg (PMF.map some) (canonical_setup_distribution setup source)
  rw [PMF.map_comp] at compiled
  exact graph.trans compiled

/-- Actual first-turn clients have the full terminal graph configuration law of canonical execution
under their disclosure-normalized profile. -/
theorem sourceServiceClientPolicy_canonicalGraph_config_distribution_eq
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat)
    (original : BehavioralProfile setup.program)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound) :
    ((application setup timeouts leaks).roundsFrom (initialDistribution setup) scheduler
      (serviceClientPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original))
      horizon).map (fun execution => execution.application.config) =
    ((setup.informationGraph.canonicalGame (setup.initialDistribution.map setup.eventInputs)).play
      (compileEventProfile setup.program (normalizeDisclosureProfile setup.program original))).map
        Subtype.val := by
  have initEq := serviceInitialDistribution_eq_inputs setup (deps := setup.informationDependencies)
  unfold initialDistribution at contract ⊢
  rw [initEq] at contract ⊢
  exact firstTurn_client_config_distribution timeouts leaks scheduler delay bound
    (setup.initialDistribution.map setup.eventInputs) _ contract timely
    (compileEventProfile_realizable fun who =>
      BehavioralPolicy.normalizeDisclosures_authentic setup.program (original who))

/-- Actual first-turn clients preserve every observation of the original source's
full typed state and public default history: the ledger-to-graph law composed with the
canonical configuration law. -/
theorem sourceServiceClientPolicy_source_observation_distribution_eq
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat)
    (original : BehavioralProfile setup.program)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound)
    {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    ((application setup timeouts leaks).roundsFrom (initialDistribution setup) scheduler
      (serviceClientPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original))
      horizon).map (fun execution =>
        (sourceReadout setup timeouts leaks
          ((application setup timeouts leaks).finished execution)).map
          (fun final => read (final.state, final.defaults))) =
      (setup.run original).map (fun final => some (read (final.state, final.defaults))) := by
  have graph := congrArg
    (PMF.map (Option.map fun final : Config Player L setup.program.terminalCtx =>
      read (final.state, final.defaults)))
    (sourceReadout_distribution_of_config_distribution setup timeouts leaks _
      (sourceServiceClientPolicy_canonicalGraph_config_distribution_eq (horizon := horizon)
        (turns := turns)
      timeouts leaks scheduler delay bound original contract timely))
  have source := congrArg
    (PMF.map fun final : Config Player L setup.program.terminalCtx =>
      some (read (final.state, final.defaults)))
    (canonical_setup_distribution setup (normalizeDisclosureProfile setup.program original))
  have normalized := congrArg (PMF.map fun output => some (read output))
    (setup.run_normalizeDisclosures_eq original)
  simp only [PMF.map_comp, Function.comp_def, Option.map_some] at graph source normalized
  exact graph.trans (source.trans normalized)

/-- Actual clients and canonical compiled graph execution preserve the same
typed-state and public-default observations for every source profile. -/
theorem sourceServiceClientPolicy_graph_observation_distribution_eq
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat)
    (original : BehavioralProfile setup.program)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound)
    {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    ((application setup timeouts leaks).roundsFrom (initialDistribution setup) scheduler
      (serviceClientPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original))
      horizon).map (fun execution =>
        (sourceReadout setup timeouts leaks
          ((application setup timeouts leaks).finished execution)).map
          (fun final => read (final.state, final.defaults))) =
      ((setup.informationGraph.canonicalGame
          (setup.initialDistribution.map setup.eventInputs)).play
        (compileEventProfile setup.program original)).map (fun terminal =>
          let final := terminalConfig setup.program terminal
          some (read (final.state, final.defaults))) := by
  rw [sourceServiceClientPolicy_source_observation_distribution_eq timeouts leaks scheduler delay
    bound original contract
    timely read]
  have law := congrArg
    (PMF.map (fun final : Config Player L setup.program.terminalCtx =>
      some (read (final.state, final.defaults)))) (canonical_setup_distribution setup original)
  simpa only [PMF.map_comp, Function.comp_def] using law.symm

end Compilation

end Vegas
