module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphDeviation
public import Vegas.Compile.EventGraphSourceResidual
public import Vegas.Compile.OpeningSafety
public import Vegas.Game.SourceServiceFacts
public import Vegas.Game.SourceServiceSiteBridge
public import Vegas.Pending.EffectiveOpeningSimulation

@[expose] public section

/-! # Source readout of physical unilateral deviations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem sourceService_deviation_config_and_readout
    (setup : Setup (Player := Player) (L := L))
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (who : Player) (deviation : (application setup timeouts leaks).Policy) :
    let players := Function.update
      (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns (firstTurnTiming setup turns) profile) who deviation
    let boundary := physicalPrefix (graph := setup.dataflowGraph) timeouts leaks scheduler
      players (setup.initialLaw.map setup.eventInputs) horizon
    ∃ policy : BehavioralPolicy who setup.program,
      (∀ rank, rank ≤ eventCount setup.program →
        (boundary rank).map (fun execution => EventGraph.Config.rankPrefix rank
          execution.application.config) =
        (setup.initialLaw.map setup.eventInputs).bind fun seed =>
          setup.informationGraph.runPlan
            (setup.informationGraph.policyPlan
              (compileEventProfile setup.program (Function.update profile who policy))
              setup.informationGraph.canonicalScheduler)
            rank (EventGraph.Config.initial seed)) ∧
      ((application setup timeouts leaks).roundsFrom (initialLaw setup) scheduler
        players horizon).map
          (fun final => sourceReadout setup timeouts leaks
            ((application setup timeouts leaks).finished final)) =
        (setup.run (Function.update profile who policy)).map some := by
  intro players boundary
  let inputs : PMF setup.informationGraph.Inputs := setup.initialLaw.map setup.eventInputs
  let reference : setup.informationGraph.BehavioralProfile :=
    compileEventProfile setup.program profile
  have safe : SafeForeignPublications (g := setup.informationGraph) inputs reference who := by
    intro event owner _ payload binding checks outputEq codeEq node
      input present config reachable ready _ action chosen disclose
    obtain ⟨value, success⟩ :=
      compileEventProfile_supported_opening_succeeds effective input present config reachable
        event ready (outputEq := outputEq) codeEq action chosen disclose
    simp [openingAccepted, node, success]
  have initialized :
      initialLaw setup = inputs.map (EventGraphRuntime.State.initial
        (graph := setup.informationGraph)) :=
    serviceInitialLaw_eq_inputs setup (deps := setup.informationDependencies)
  have inputContract : AsyncContract timeouts leaks (inputs.map EventGraphRuntime.State.initial)
      horizon scheduler delay bound := by
    rw [← initialized]
    exact contract
  obtain ⟨replacement, prefixes, raw⟩ := safePublication_deviation_config_law
    (graph := setup.dataflowGraph) (turns := turns) timeouts leaks scheduler delay bound
    inputs reference inputContract timely who deviation safe
  rw [← initialized] at raw
  let translated := backtranslateEventPolicy setup.program who replacement
  let updated := Function.update reference who replacement
  let compiled := compileEventProfile setup.program (Function.update profile who translated)
  have runs (seed : setup.informationGraph.Inputs) :
      setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler updated seed =
        setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler
          compiled seed := by
    exact (canonical_deviation_runPolicies_law setup.program profile who replacement seed).symm
  refine ⟨translated, ?_, ?_⟩
  · intro rank bounded
    refine (prefixes rank bounded).trans ?_
    apply bind_congr_on_support _
    intro seed _
    have sliced := congrArg (PMF.map (EventGraph.Config.rankPrefix rank)) (runs seed)
    rwa [runPolicies_rankPrefix updated seed rank bounded,
      runPolicies_rankPrefix compiled seed rank bounded] at sliced
  · have gameLaw := setup.informationGraph.gameForm_play_map_val
      inputs setup.informationGraph.canonicalScheduler compiled
    have whole : inputs.bind (setup.informationGraph.runPolicies
        setup.informationGraph.canonicalScheduler updated) =
        inputs.bind (setup.informationGraph.runPolicies
          setup.informationGraph.canonicalScheduler compiled) :=
      bind_congr_on_support _ fun seed _ => runs seed
    have graph := sourceReadout_law_of_config_law setup timeouts leaks compiled
      (raw.trans (whole.trans gameLaw.symm))
    have source := congrArg (PMF.map some)
      (canonical_setup_law setup (Function.update profile who translated))
    refine graph.trans ?_
    simpa only [PMF.map_comp, Function.comp_def, compiled] using source

/-- One source deviation realizes the terminal readout and every decoded physical rank. -/
theorem sourceService_deviation_prefix_readout_law [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (who : Player) (deviation : (application setup timeouts leaks).Policy) :
    let players := Function.update
      (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns (firstTurnTiming setup turns) profile) who deviation
    let boundary := physicalPrefix (graph := setup.dataflowGraph) timeouts leaks scheduler
      players (setup.initialLaw.map setup.eventInputs) horizon
    ∃ policy : BehavioralPolicy who setup.program,
      (∀ rank, rank ≤ eventCount setup.program →
        (boundary rank).map (fun execution => sourceServicePrefix? setup rank
          (EventGraph.Config.rankPrefix rank execution.application.config)) =
        (setup.initialLaw.bind fun initial =>
          (fun law => law.bind (ProtocolState.behavioralStateStep setup.program
            (Function.update profile who policy)))^[rank]
            (PMF.pure (ProtocolState.entry setup.program (Config.initial initial)))).map some) ∧
      ((application setup timeouts leaks).roundsFrom (initialLaw setup) scheduler
        players horizon).map
          (fun final => sourceReadout setup timeouts leaks
            ((application setup timeouts leaks).finished final)) =
        (setup.run (Function.update profile who policy)).map some := by
  intro players boundary
  obtain ⟨policy, prefixes, terminal⟩ :=
    sourceService_deviation_config_and_readout setup timeouts leaks horizon scheduler delay bound
      turns contract timely profile effective who deviation
  refine ⟨policy, ?_, terminal⟩
  intro rank bounded
  have decoded := congrArg (PMF.map (sourceServicePrefix? setup rank)) (prefixes rank bounded)
  rw [PMF.map_comp, Function.comp_def] at decoded
  exact decoded.trans (compileEventProfile_initial_prefix_law setup
    (Function.update profile who policy) rank bounded)

/-- Against first-turn clients, every physical policy of one player has exactly
the terminal source-configuration law of one behavioral source deviation. -/
theorem sourceService_deviation_readout_law
    (setup : Setup (Player := Player) (L := L))
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (who : Player) (deviation : (application setup timeouts leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((application setup timeouts leaks).roundsFrom (initialLaw setup) scheduler
        (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
          leaks bound turns
          (firstTurnTiming setup turns) profile) who deviation) horizon).map
          (fun final => sourceReadout setup timeouts leaks
            ((application setup timeouts leaks).finished final)) =
        (setup.run (Function.update profile who policy)).map some := by
  obtain ⟨policy, _, terminal⟩ :=
    sourceService_deviation_config_and_readout setup timeouts leaks horizon scheduler delay bound
      turns contract timely profile effective who deviation
  exact ⟨policy, terminal⟩

end Vegas
