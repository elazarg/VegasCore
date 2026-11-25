module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ServiceRosterHistory
public import Vegas.Pending.ServiceRosterContract

@[expose] public section

/-! # The public roster scheduler satisfies the asynchronous contract

All initialized raw histories satisfy one calendar invariant, including native
automatic completion. Obsolete blocks retain responses without advancing time.
The resulting reaction, inclusion and completion guarantees hold for arbitrary
player strategies, pending observations and network policies.
-/

noncomputable section

namespace Vegas

open Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A sole authored response for a ready event receives a receipt before time advances. -/
theorem rosterScheduler_protectedInclusion (graph : EventGraph Player L)
    (inputs : PMF graph.Inputs)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (rosters : graph.EventId → List Player)
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks) :
    ProtectedInclusion (rosterTimeouts graph) leaks (rosterInitialDistribution graph inputs)
      (rosterPlan graph rosters).length
      (rosterScheduler graph leaks rosters network) (fun _ => 0) :=
  RosterCalendarInvariant.protectedInclusion graph inputs leaks rosters
    (rosterScheduler graph leaks rosters network)
    (fun _ trace => RosterCalendarInvariant.history graph inputs leaks rosters network trace)

/-- The fixed command horizon completes the graph under arbitrary responses. -/
theorem rosterScheduler_completesPlay (graph : EventGraph Player L)
    (inputs : PMF graph.Inputs)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (rosters : graph.EventId → List Player)
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks) :
    CompletesPlay (rosterTimeouts graph) leaks (rosterInitialDistribution graph inputs)
      (rosterPlan graph rosters).length
      (rosterScheduler graph leaks rosters network) :=
  RosterCalendarInvariant.completesPlay graph inputs leaks rosters
    (rosterScheduler graph leaks rosters network)
    (fun _ trace => RosterCalendarInvariant.history graph inputs leaks rosters network trace)

/-- The roster scheduler supplies rank-bounded activation, zero-time protected
inclusion and terminal completion. Each event's actor must occur in its roster. -/
theorem rosterScheduler_asyncContract (graph : EventGraph Player L)
    (inputs : PMF graph.Inputs)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (rosters : graph.EventId → List Player)
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks)
    (opportunities : ActorOpportunities graph rosters) :
    AsyncContract (rosterTimeouts graph) leaks (rosterInitialDistribution graph inputs)
      (rosterPlan graph rosters).length
      (rosterScheduler graph leaks rosters network) (fun event => event.val) (fun _ => 0) where
  opportunity := RosterCalendarInvariant.opportunity graph inputs leaks rosters
    (rosterScheduler graph leaks rosters network)
    (fun _ trace => RosterCalendarInvariant.history graph inputs leaks rosters network trace)
    opportunities
  inclusion := rosterScheduler_protectedInclusion graph inputs leaks rosters network
  completes := rosterScheduler_completesPlay graph inputs leaks rosters network

omit [DecidableEq Player] in
/-- Reaction and protected inclusion fit strictly within every rank deadline. -/
theorem rosterScheduler_asyncTimely (graph : EventGraph Player L) :
    AsyncTimely (rosterTimeouts graph) (fun event => event.val) (fun _ => 0) := by
  intro event _
  change event.val + 0 < event.val + 1
  omega

end Vegas
