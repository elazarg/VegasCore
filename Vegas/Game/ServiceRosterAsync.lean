/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceRosterHistory
import Vegas.Game.ServiceRosterContract

/-! # The public roster scheduler satisfies the asynchronous contract

All initialized raw histories satisfy one calendar invariant, including native
automatic completion. Obsolete blocks retain responses without advancing time.
The resulting reaction, inclusion and completion guarantees hold for arbitrary
player strategies, pending observations and network policies.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A sole authored response for a ready event receives a receipt before time advances. -/
theorem rosterScheduler_protectedInclusion (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) :
    ProtectedInclusion (runtime setup) leaks (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) (fun _ => 0) :=
  RosterCalendarInvariant.protectedInclusion setup leaks rosters network
    (fun _ trace => RosterCalendarInvariant.history setup leaks rosters network trace)

/-- The fixed command horizon completes the graph under arbitrary responses. -/
theorem rosterScheduler_completesPlay (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) :
    CompletesPlay (runtime setup) leaks (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) :=
  RosterCalendarInvariant.completesPlay setup leaks rosters network
    (fun _ trace => RosterCalendarInvariant.history setup leaks rosters network trace)

/-- The roster scheduler supplies rank-bounded activation, zero-time protected
inclusion and terminal completion. Each event's actor must occur in its roster. -/
theorem rosterScheduler_asyncContract (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (opportunities : ActorOpportunities setup rosters) :
    AsyncContract (runtime setup) leaks (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) (fun event => event.val) (fun _ => 0) where
  opportunity := RosterCalendarInvariant.opportunity setup leaks rosters network
    (fun _ trace => RosterCalendarInvariant.history setup leaks rosters network trace) opportunities
  inclusion := rosterScheduler_protectedInclusion setup leaks rosters network
  completes := rosterScheduler_completesPlay setup leaks rosters network

/-- Reaction and protected inclusion fit strictly within every rank deadline. -/
theorem rosterScheduler_asyncTimely (setup : Setup (Player := Player) (L := L)) :
    AsyncTimely (runtime setup) (fun event => event.val) (fun _ => 0) := by
  intro event _
  change event.val + 0 < event.val + 1
  omega

end Vegas
