module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.FirstTurnSimulation
public import Vegas.Pending.TurnClientRecovery

@[expose] public section

/-! # Recovered clients realize the sequential graph configuration law -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- At each reached boundary of the recovered clients, the next completed ledger configuration
realizes the graph event step followed by automatic completion. -/
theorem firstTurn_client_event_config_distribution
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    {horizon turns : Nat} (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (delay bound : graph.sequentialize.EventId → Nat)
    (inputs : PMF graph.sequentialize.Inputs) (reference : graph.sequentialize.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (realizable : RealizableProfile (graph := graph.sequentialize) inputs reference)
    (event : graph.sequentialize.EventId)
    (execution : (reactiveApplication timeouts leaks).Execution)
    (boundary : PrefixBoundary (inputs.map State.initial) scheduler
      (clientPolicy timeouts leaks bound turns
        (EventGraphRuntime.firstTurnTiming graph.sequentialize turns) reference) event.val
        execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    let players := clientPolicy timeouts leaks
      bound turns
      (EventGraphRuntime.firstTurnTiming graph.sequentialize turns) reference
    ((reactiveApplication timeouts leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).map
        (fun final => final.application.config) =
      (EventGraph.eventStep reference
        execution.application.config event (boundary.ordered.ready event.isLt)).map
          State.drainConfig := by
  classical
  dsimp only
  rw [clientPolicy_runUntilHorizon timeouts leaks (inputs.map State.initial) scheduler bound turns
    _ reference _ horizon execution boundary.supported]
  have supported := boundary.supported
  rw [clientPolicy_roundsFrom] at supported
  exact firstTurn_event_config_distribution timeouts leaks scheduler delay bound inputs reference
    contract
    timely realizable event execution ⟨supported, boundary.ordered, boundary.untouched⟩ bounded

/-- The recovered clients realize the full canonical sequential graph configuration law. -/
theorem firstTurn_client_config_distribution
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    {horizon turns : Nat} (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (delay bound : graph.EventId → Nat) (inputs : PMF graph.sequentialize.Inputs)
    (reference : graph.sequentialize.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (realizable : RealizableProfile (graph := graph.sequentialize) inputs reference) :
    ((reactiveApplication timeouts leaks).roundsFrom (inputs.map State.initial) scheduler
      (clientPolicy timeouts leaks bound turns
        (EventGraphRuntime.firstTurnTiming graph.sequentialize turns) reference) horizon).map
        (fun execution => execution.application.config) =
      ((graph.sequentialize.canonicalGame inputs).play reference).map Subtype.val := by
  rw [clientPolicy_roundsFrom]
  exact firstTurn_config_distribution timeouts leaks scheduler delay bound inputs reference
    contract timely
    realizable

end Vegas.EventGraphRuntime
