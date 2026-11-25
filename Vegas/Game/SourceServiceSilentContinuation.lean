module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceCompletion
public import Vegas.Game.SourceServiceFacts
public import Vegas.Pending.SilentContinuation

@[expose] public section


/-! # Native continuation at a silent source instruction

When an owner is silent while its head event is ready, pending messages cannot
complete that event if none of its own pending calls names it. The native
runtime completes it by expiry. Composing the resulting endpoint with the
ordinary graph continuation gives the silent source step's full continuation,
including every automatic completion after default.

At an initialized untouched boundary, own-submission-at-turn discipline already
implies the required pending-message fact. Other players and the scheduler are
arbitrary; completion by the horizon is supplied by the ordinary service contract.
-/

noncomputable section
namespace Vegas
open SourceProgram EventGraphRuntime EventGraph GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}

/-- At an initialized execution where `event` is untouched, a player whose
prior submissions were at its turn has no pending call for it. -/
theorem Untouched.no_pending_of_ownSubmissions (timeouts : EventTimeouts
    (serviceGraph setup deps))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : (serviceGraph setup deps).EventId) (execution :
      ((reactiveApplication timeouts) leaks).Execution)
    (supported : execution ∈ (((reactiveApplication timeouts) leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler players execution.environmentRecall.length).support)
    (untouched : Untouched setup leaks event execution)
    (owner : Player) (truthful : OwnSubmissionsAtTurn setup leaks execution owner) :
    ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (serviceGraph setup deps) ≠ some event :=
  EventGraphRuntime.untouched_no_pending_of_ownSubmissions timeouts leaks scheduler players event
    execution supported untouched owner truthful

/-- At an untouched initialized boundary, a player whose prior submissions
were at its turn has no pending call for the head event. -/
theorem CompletionBoundary.no_pending_of_ownSubmissions (timeouts : EventTimeouts
  setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (scheduler : (application setup timeouts leaks).Scheduler)
    (players : Player → (application setup timeouts leaks).Policy)
    (event : setup.informationGraph.EventId) (execution : (application setup timeouts
      leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (owner : Player) (truthful : OwnSubmissionsAtTurn setup leaks execution owner) :
    ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? setup.informationGraph ≠ some event :=
  Untouched.no_pending_of_ownSubmissions timeouts leaks scheduler players event execution
    boundary.supported (boundary.untouched event le_rfl) owner truthful

/-- Silence at an owned ready head has the same continuation as the source
omission, even when expiry automatically completes further events. The initial
execution may be any actual raw idle history. -/
theorem silent_runUntil_bind_continuation
    (timeouts : EventTimeouts (serviceGraph setup deps))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {Result : Type*} (continuation : (serviceGraph setup deps).Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State (serviceGraph setup deps),
      continuation state.drain.config = continuation state.config)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (horizon : Nat)
    (complete : CompletesPlay timeouts leaks (serviceInitialLaw setup deps) horizon scheduler)
    (event : (serviceGraph setup deps).EventId) (solitary :
      (serviceGraph setup deps).Solitary event) (owner : Player)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (action : (serviceGraph setup deps).Action event) (silent : SilentAction event action)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    {remaining : Nat}
    (trace : (((reactiveApplication timeouts) leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (serviceGraph setup deps) ≠ some event)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩) :
    ((((reactiveApplication timeouts) leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        continuation stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        continuation after :=
  EventGraphRuntime.silent_runUntil_bind_continuation timeouts leaks continuation drained
    scheduler players horizon complete event solitary owner owned action silent execution ready
    (legalFacts setup leaks horizon scheduler _ trace).quiescent trace safe quiet

/-- Silence at an owned ready head has the same continuation as the source
omission, even when expiry automatically completes further events. The initial
execution may be any actual raw idle history. -/
theorem silent_runUntil_bind_runPlan
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (profile : setup.informationGraph.BehavioralProfile)
    (scheduler : (application setup timeouts leaks).Scheduler)
    (players : Player → (application setup timeouts leaks).Policy)
    (horizon : Nat)
    (complete : CompletesPlay timeouts leaks (initialLaw setup) horizon scheduler)
    (event : setup.informationGraph.EventId) (owner : Player)
    (owned : setup.informationGraph.actor? event = some owner)
    (action : setup.informationGraph.Action event) (silent : SilentAction event action)
    (execution : (application setup timeouts leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    {remaining : Nat}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? setup.informationGraph ≠ some event)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩) :
    (((application setup timeouts leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        setup.informationGraph.runPlan (setup.informationGraph.policyPlan profile
          setup.informationGraph.canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        setup.informationGraph.runPlan (setup.informationGraph.policyPlan profile
          setup.informationGraph.canonicalScheduler)
          after.remaining after :=
  silent_runUntil_bind_continuation timeouts leaks
    (fun config => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan profile setup.informationGraph.canonicalScheduler)
        config.remaining config)
    (fun state => (EventGraphRuntime.State.drain_runPlan_canonical setup.informationGraph profile
      state).symm) scheduler players horizon complete event
    (setup.informationGraph.sequentialize_solitary event) owner owned action silent execution ready
    trace safe quiet

end Vegas
