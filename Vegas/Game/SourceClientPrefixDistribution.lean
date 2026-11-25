module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceFirstTurnCompletion
public import Vegas.Pending.StoppedPrefixDistribution
public import Vegas.Source.BehavioralPrefixReadout

@[expose] public section

/-! # Source protocol states at physical client completion boundaries -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}

/-- Stop the actual clients when a given compiled event first completes. Reading
the configuration through that event's rank gives the entire source protocol
state law after that many instructions of the disclosure-normalized profile. -/
theorem sourceServiceClientPolicy_stopped_prefix_distribution
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat)
    (original : BehavioralProfile setup.program)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound) (event : setup.informationGraph.EventId) :
    let profile := normalizeDisclosureProfile setup.program original
    let app := application setup timeouts leaks
    let players := serviceClientPolicy setup setup.informationDependencies timeouts.duration leaks
      bound turns (firstTurnTiming setup turns) profile
    let rank := event.val + 1
    (setup.initialDistribution.bind fun seed => (app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (ReactiveApplication.Execution.initial app (EventGraphRuntime.State.initial
        (setup.eventInputs seed)))).map fun stopped =>
          sourceServicePrefix? setup rank (EventGraph.Config.rankPrefix rank
            stopped.application.config)) =
      (setup.initialDistribution.bind fun seed =>
        (fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[rank]
          (PMF.pure (ProtocolState.entry setup.program (Config.initial seed)))).map some := by
  intro profile app players rank
  let inputs := setup.initialDistribution.map setup.eventInputs
  let reference := compileEventProfile setup.program profile
  have full := sourceServiceClientPolicy_canonicalGraph_config_distribution_eq
    (turns := turns) timeouts leaks
    scheduler delay bound original contract timely
  have initEq := serviceInitialDistribution_eq_inputs setup (deps := setup.informationDependencies)
  unfold initialDistribution at contract full
  rw [initEq] at contract full
  have native := stopped_prefix_of_config_distribution (graph := setup.dataflowGraph) timeouts leaks
    scheduler players horizon inputs contract.completes reference
    (full.trans (EventGraph.gameForm_play_map_val _ _ _ _)) event
  have decoded := congrArg (PMF.map (sourceServicePrefix? setup rank)) native
  have compiled := compileEventProfile_initial_prefix_distribution setup profile rank event.isLt
  refine Eq.trans ?_ (decoded.trans compiled)
  simp only [PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def, inputs]
  rfl

/-- The stopped clients preserve the original profile's typed cells and public defaults
at the completed source instruction. -/
theorem sourceServiceClientPolicy_stopped_prefix_readout_distribution
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat)
    (original : BehavioralProfile setup.program)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound) (event : setup.informationGraph.EventId) :
    let profile := normalizeDisclosureProfile setup.program original
    let app := application setup timeouts leaks
    let players := serviceClientPolicy setup setup.informationDependencies timeouts.duration leaks
      bound turns (firstTurnTiming setup turns) profile
    let rank := event.val + 1
    (setup.initialDistribution.bind fun seed => (app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (ReactiveApplication.Execution.initial app (EventGraphRuntime.State.initial
        (setup.eventInputs seed)))).map fun stopped =>
          (sourceServicePrefix? setup rank (EventGraph.Config.rankPrefix rank
            stopped.application.config)).map (ProtocolState.prefixReadout setup.program)) =
      (setup.initialDistribution.bind fun seed =>
        (fun law => law.bind (ProtocolState.behavioralStateStep setup.program original))^[rank]
          (PMF.pure (ProtocolState.entry setup.program (Config.initial seed)))).map
            (fun point => some (ProtocolState.prefixReadout setup.program point)) := by
  intro profile app players rank
  let read := ProtocolState.prefixReadout setup.program
  let readTerminal := terminalPrefixReadout setup.program rank
  have physical := congrArg (PMF.map (Option.map read))
    (sourceServiceClientPolicy_stopped_prefix_distribution (turns := turns) timeouts leaks
      scheduler delay bound original contract timely event)
  have before := congrArg (PMF.map some) (setup.behavioralStatePrefix_readout_eq profile rank)
  have after := congrArg (PMF.map some) (setup.behavioralStatePrefix_readout_eq original rank)
  have terminal := congrArg (PMF.map (fun final => some (readTerminal final)))
    (setup.run_normalizeDisclosures_eq original)
  simp only [PMF.map_comp, Function.comp_def, Option.map_some] at physical before after terminal
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using
    physical.trans (before.trans (terminal.trans after.symm))

end Vegas
