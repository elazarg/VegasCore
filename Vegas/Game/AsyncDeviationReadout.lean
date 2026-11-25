module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.AsyncDeviationDistribution
public import Vegas.Source.BehavioralPrefixReadout
public import Vegas.Source.DisclosureBehavioral

@[expose] public section

/-! # Typed outcome of physical unilateral deviations

The ledger realizes the deviator at the event graph's canonical checkpoints.
Compiler backtranslation gives one source policy across the initial law.
Normalizing the other players' disclosures preserves the typed terminal state
and public default record used by the original source game.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every raw physical unilateral deviation against compiled first-turn clients
has the typed-state and public-default law of a behavioral source deviation. -/
theorem asyncDeviation_readout_distribution
    (setup : Setup (Player := Player) (L := L))
    {duration : setup.informationGraph.EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} {scheduler : (application setup ⟨duration⟩ leaks).Scheduler}
    {delay bound : setup.informationGraph.EventId → Nat}
    (contract : AsyncContract ⟨duration⟩ leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely ⟨duration⟩ delay bound) (turns : Nat)
    (original : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup ⟨duration⟩ leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((application setup ⟨duration⟩ leaks).roundsFrom
        (initialDistribution setup) scheduler
        (Function.update (serviceTurnPolicy setup setup.informationDependencies duration leaks
          bound turns
          (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original))
          who deviation) horizon).map (fun execution =>
            (sourceReadout setup ⟨duration⟩ leaks
              ((application setup ⟨duration⟩ leaks).finished execution)).map
                (fun final => (final.state, final.defaults))) =
        (setup.run (Function.update original who policy)).map
          (fun final => some (final.state, final.defaults)) := by
  obtain ⟨policy, physical⟩ := sourceService_deviation_readout_distribution_eq setup ⟨duration⟩
    leaks
    horizon scheduler delay bound turns contract timely
    (normalizeDisclosureProfile setup.program original)
    who
    (fun player _ => BehavioralPolicy.normalizeDisclosures_effective
      setup.program (original player))
    deviation
  refine ⟨policy, ?_⟩
  have projected := congrArg (PMF.map (Option.map (fun final => (final.state, final.defaults))))
    physical
  have normalized := congrArg (PMF.map some)
    (setup.run_update_normalizeDisclosures_eq original who policy)
  simp only [PMF.map_comp, Function.comp_def, Option.map_some] at projected normalized
  exact projected.trans normalized

/-- Against the recovered clients of an arbitrary original profile, a physical unilateral
deviation has the same typed-state and public-default law as a source deviation against
the original opponents. -/
theorem asyncClientDeviation_readout_distribution
    (setup : Setup (Player := Player) (L := L))
    {duration : setup.informationGraph.EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} {scheduler : (application setup ⟨duration⟩ leaks).Scheduler}
    {delay bound : setup.informationGraph.EventId → Nat}
    (contract : AsyncContract ⟨duration⟩ leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely ⟨duration⟩ delay bound) (turns : Nat)
    (original : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup ⟨duration⟩ leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((application setup ⟨duration⟩ leaks).roundsFrom
        (initialDistribution setup) scheduler
        (Function.update (serviceClientPolicy setup setup.informationDependencies duration leaks
          bound turns
          (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original))
          who deviation) horizon).map (fun execution =>
            (sourceReadout setup ⟨duration⟩ leaks
              ((application setup ⟨duration⟩ leaks).finished execution)).map
                (fun final => (final.state, final.defaults))) =
        (setup.run (Function.update original who policy)).map
          (fun final => some (final.state, final.defaults)) := by
  rw [sourceServiceClientPolicy_deviation_roundsFrom scheduler bound turns
    (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original)
    who deviation horizon]
  exact asyncDeviation_readout_distribution setup leaks contract timely turns original who deviation

/-- The same source deviation matches the typed cells and public defaults at each prefix and
at terminal readout against the original opponents. -/
theorem asyncClientDeviation_prefix_and_readout_distributions_eq [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely timeouts delay bound)
    (original : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup timeouts leaks).Policy) :
    let normalized := normalizeDisclosureProfile setup.program original
    let players := Function.update
      (serviceClientPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns (firstTurnTiming setup turns) normalized) who deviation
    let boundary := physicalPrefix (graph := setup.dataflowGraph) timeouts leaks scheduler
      players (setup.initialDistribution.map setup.eventInputs) horizon
    ∃ policy : BehavioralPolicy who setup.program,
      (∀ rank, rank ≤ eventCount setup.program →
        (boundary rank).map (fun execution =>
          (sourceServicePrefix? setup rank
            (EventGraph.Config.rankPrefix rank execution.application.config)).map
              (ProtocolState.prefixReadout setup.program)) =
        (setup.initialDistribution.bind fun initial =>
          (fun law => law.bind (ProtocolState.behavioralStateStep setup.program
            (Function.update original who policy)))^[rank]
            (PMF.pure (ProtocolState.entry setup.program (Config.initial initial)))).map
              (fun point => some (ProtocolState.prefixReadout setup.program point))) ∧
      ((application setup timeouts leaks).roundsFrom (initialDistribution setup) scheduler
        players horizon).map (fun execution =>
          (sourceReadout setup timeouts leaks
            ((application setup timeouts leaks).finished execution)).map
              (fun final => (final.state, final.defaults))) =
        (setup.run (Function.update original who policy)).map
          (fun final => some (final.state, final.defaults)) := by
  intro normalized players boundary
  obtain ⟨policy, prefixLaw, terminalLaw⟩ :=
    sourceService_deviation_prefix_and_readout_distributions_eq setup timeouts leaks horizon
      scheduler delay bound turns contract timely normalized who
      (fun player _ =>
        BehavioralPolicy.normalizeDisclosures_effective setup.program (original player)) deviation
  have normalization := setup.run_update_normalizeDisclosures_eq original who policy
  refine ⟨policy, ?_, ?_⟩
  · intro rank bounded
    let read := ProtocolState.prefixReadout setup.program
    let readTerminal := terminalPrefixReadout setup.program rank
    have physical := congrArg (PMF.map (Option.map read)) (prefixLaw rank bounded)
    have before := congrArg (PMF.map some)
      (setup.behavioralStatePrefix_readout_eq (Function.update normalized who policy) rank)
    have after := congrArg (PMF.map some)
      (setup.behavioralStatePrefix_readout_eq (Function.update original who policy) rank)
    have terminal := congrArg (PMF.map (fun final => some (readTerminal final))) normalization
    simp only [PMF.map_comp, Function.comp_def, Option.map_some] at physical before after terminal
    exact physical.trans (before.trans (terminal.trans after.symm))
  · have projected := congrArg (PMF.map (Option.map (fun final => (final.state, final.defaults))))
      terminalLaw
    have normalized := congrArg (PMF.map some) normalization
    simp only [PMF.map_comp, Function.comp_def, Option.map_some] at projected normalized
    exact projected.trans normalized

end Vegas
