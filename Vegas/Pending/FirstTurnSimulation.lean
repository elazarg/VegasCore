module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.FirstTurnAction
public import Vegas.Pending.FirstTurnMixture
public import Vegas.Pending.GraphEventStepDistribution
public import Vegas.Pending.ChanceCompletionConfig
public import Vegas.Pending.TurnClientActionDistribution

@[expose] public section

/-! # Probabilistic simulation at ledger event boundaries -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- At a sequential event boundary the stopped configuration has the graph
step and automatic drain law whenever the ready event's owner follows the
reference first-turn policy. All other native policies may vary freely. -/
theorem firstTurn_event_config_distribution_of_owner_follows
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
    (players : Player → (reactiveApplication timeouts leaks).Policy)
    (follows : ∀ owner, graph.sequentialize.actor? event = some owner →
      players owner = turnPolicy timeouts leaks bound turns
        (EventGraphRuntime.firstTurnTiming graph.sequentialize turns) reference owner)
    (execution : (reactiveApplication timeouts leaks).Execution)
    (boundary : PrefixBoundary (inputs.map State.initial) scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    ((reactiveApplication timeouts leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).map
        (fun final => final.application.config) =
      (EventGraph.eventStep reference
        execution.application.config event (boundary.ordered.ready event.isLt)).map
          State.drainConfig := by
  classical
  let app := reactiveApplication timeouts leaks
  let stopped := app.runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon execution
  have ready := boundary.ordered.ready event.isLt
  have progress (final : app.Execution) (reached : final ∈ stopped.support) :=
    runUntilHorizon_event_progress contract.completes event execution final boundary.supported
      bounded ready.1 reached
  cases owned : graph.sequentialize.actor? event with
  | none =>
      simp only [EventGraph.eventStep, EventGraph.actionDistribution_of_ownerless _ _ owned,
        PMF.pure_bind]
      exact chance_completed_config_distribution timeouts leaks
        (fun node => (graph.sequentialize_solitary node).ownerSolitary)
        scheduler players event owned (graph.sequentialize_solitary event) _
        execution ready (fun final reached => (progress final reached).2.2.1)
  | some owner =>
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler
        players execution.environmentRecall.length bounded execution boundary.supported
      obtain ⟨initial, supported, valid⟩ := reactive_history_invariant timeouts leaks
        inputs horizon scheduler trace
      let law := EventGraph.actionDistribution reference execution.application.config event
      have mixture := firstTurn_mixture timeouts leaks scheduler bound reference owner event owned
        players (follows owner owned) execution (fun _ other =>
          graph.sequentialize_solitary event _ other ready)
        boundary.supported (boundary.untouched event le_rfl owner) bounded law
        (fun current same selected => by
          simpa only [same] using referencePolicy_actionDistribution timeouts leaks reference owner
            current
            event selected owned)
      let drain := fun config : graph.sequentialize.Config => PMF.pure (State.drainConfig config)
      calc
        _ = stopped.map (fun final => State.drainConfig final.application.config) := by
          apply map_congr_on_support _
          intro final reached
          obtain ⟨seen, within, _⟩ := progress final reached
          obtain ⟨later⟩ := app.raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler
            players final.environmentRecall.length within final seen
          exact (State.drainConfig_of_quiescent final.application
            (legalFacts timeouts leaks inputs horizon scheduler _ later).quiescent).symm
        _ = _ := by
          dsimp only [stopped]
          rw [mixture, EventGraph.eventStep, PMF.map_bind, PMF.map_bind]
          apply bind_congr_on_support _
          intro action member
          have fixed := firstTurn_fixedAction_continuation timeouts leaks scheduler delay
            bound reference drain
            (fun state => congrArg PMF.pure (State.drainConfig_drain_eq state))
            contract timely owner event owned (graph.sequentialize_solitary event)
            players (follows owner owned) action execution ready boundary.supported
            (boundary.untouched event le_rfl) bounded
            (realizable initial supported _ valid.reachable event ready action member)
          rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
          exact fixed

/-- From each reached sequential event boundary, the next completed ledger configuration has
the law of the graph action and step followed by automatic completion. -/
theorem firstTurn_event_config_distribution
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
      (turnPolicy timeouts leaks bound turns
        (EventGraphRuntime.firstTurnTiming graph.sequentialize turns) reference) event.val
        execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    let players := turnPolicy timeouts leaks
      bound turns
      (EventGraphRuntime.firstTurnTiming graph.sequentialize turns) reference
    ((reactiveApplication timeouts leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).map
        (fun final => final.application.config) =
      (EventGraph.eventStep reference
        execution.application.config event (boundary.ordered.ready event.isLt)).map
          State.drainConfig := by
  exact firstTurn_event_config_distribution_of_owner_follows timeouts leaks scheduler delay bound
    inputs reference contract timely realizable event _ (fun _ _ => rfl) execution boundary bounded

/-- Sequential first-turn clients realize the full canonical graph configuration distribution. -/
theorem firstTurn_config_distribution
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
      (turnPolicy timeouts leaks bound turns (EventGraphRuntime.firstTurnTiming graph.sequentialize
        turns) reference) horizon).map (fun execution => execution.application.config) =
      ((graph.sequentialize.canonicalGame inputs).play reference).map Subtype.val :=
  config_distribution_of_event_steps inputs reference contract.completes
    (firstTurn_event_config_distribution timeouts leaks scheduler delay bound inputs reference
      contract timely realizable)

end Vegas.EventGraphRuntime
