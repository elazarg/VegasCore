module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.TurnSubmissionDiscipline
public import Vegas.Pending.SilentContinuation
public import Vegas.Pending.FixedOpportunity

@[expose] public section

/-! # A fixed silent first callback realizes the graph omission -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem fixed_silent_client_quiet
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bound : graph.EventId → Nat) (turns : Nat)
    (client : graph.BehavioralProfile) (owner : Player)
    (event : graph.EventId) (action : graph.Action event)
    (silent : SilentAction event action)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (serving : view.application.publicView.ownTurn? owner = some event) :
    (if turnIndex timeouts leaks owner event past view = some 0 then
      fixedOpportunity timeouts leaks bound owner event action past view
    else turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) client owner past view) =
      PMF.pure ⟨none⟩ := by
  by_cases first :
      turnIndex timeouts leaks owner event past view = some 0
  · rw [ite_eq_left first]
    exact fixedOpportunity_silent action past view
      (canonicalServiceDecision_silent owner past view event action silent)
  · rw [ite_eq_right first]
    by_cases owned : graph.actor? event = some owner
    · exact turnPolicy_later owned serving first
    · simp only [turnPolicy, serving, owned, ↓reduceDIte,
        ReactiveApplication.silentPolicy_apply]

/-- Fixing a silent first-turn action has that action's full graph continuation
from an initialized untouched execution, under arbitrary policies of other players. -/
theorem firstTurn_fixed_silent_continuation
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) {horizon turns : Nat}
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (delay bound : graph.EventId → Nat)
    (client : graph.BehavioralProfile) {Result : Type*} (continuation :
      graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (contract : AsyncContract timeouts leaks
      (inputs.map State.initial) horizon scheduler delay bound)
    (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner) (solitary :
      graph.Solitary event)
    (background : Player → ((reactiveApplication timeouts) leaks).Policy)
    (follows : background owner = turnPolicy timeouts leaks
      bound turns (EventGraphRuntime.firstTurnTiming graph turns) client owner)
    (action : graph.Action event) (silent : SilentAction event action)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (supported : execution ∈ (((reactiveApplication timeouts) leaks).roundsFrom
      (inputs.map State.initial) scheduler background
        execution.environmentRecall.length).support)
    (untouched : ∀ who, ∀ entry ∈ execution.logs who,
      ¬ entry.beforeView.application.publicView.EventReady event)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    let players := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) client
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
  classical
  let app := (reactiveApplication timeouts) leaks
  let players := turnPolicy timeouts leaks bound turns
    (EventGraphRuntime.firstTurnTiming graph turns) client
  let member := fun past view =>
    if turnIndex timeouts leaks owner event past view = some 0 then
      fixedOpportunity timeouts leaks bound owner event action past view
    else players owner past view
  have atTurn : SubmitsAtTurn timeouts leaks (background owner) owner := by
    rw [follows]
    exact turnPolicy_submitsAtTurn timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns)
      client owner
  have truthful : OwnSubmissionsAtTurn timeouts leaks execution owner :=
    SubmitsAtTurn.roundsFrom timeouts leaks atTurn (inputs.map State.initial)
      execution.environmentRecall.length execution
      supported
  have safe := untouched_no_pending_of_ownSubmissions timeouts leaks scheduler background event
    execution supported untouched owner truthful
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler
    background
    execution.environmentRecall.length bounded execution supported
  apply silent_runUntil_bind_continuation timeouts leaks continuation drained scheduler
    (Function.update background owner member) horizon contract.completes event solitary owner
      owned action
      silent execution ready
      (reactive_history_quiescent timeouts leaks inputs horizon scheduler trace)
    trace safe
  intro past view serving
  rw [Function.update_self]
  exact fixed_silent_client_quiet timeouts leaks bound turns client owner event action silent past
    view serving

end Vegas.EventGraphRuntime
