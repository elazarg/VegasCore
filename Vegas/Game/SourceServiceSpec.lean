/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMenu
import Vegas.Game.ServiceRoster
import Vegas.Game.RevealServicePayoffs
import Vegas.Pending.ReactiveBoundedValues
import Vegas.Source.SetupProtocol

/-! # The fixed full-source native service

The service specification packages setup, observation, message bounds and the
public roster scheduler with their structural compiler conditions. Its basic
information models and readout do not depend on continuation-comparison proofs.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The fixed full-source native service: the program setup, passive observation
rule, message bounds, activation rosters and public network policy, together
with the compiler's side conditions on them. -/
structure SourceServiceSpec (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] where
  setup : Setup (Player := Player) (L := L)
  leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))
  bounds : MessageBounds (graph setup)
  rosters : (graph setup).EventId → List Player
  network : (runtime setup).NetworkPolicy leaks
  /-- Every binding value the source can choose has a native message form. -/
  values : bounds.CoversBindingValues
  /-- Every supported initial binding table fits the candidate catalogue. -/
  initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state
  /-- The candidate catalogue has a slot for every event. -/
  capacity : (graph setup).order.eventCount ≤ bounds.candidateCount
  /-- Every event actor has an activation at its own event. -/
  opportunities : ActorOpportunities setup rosters
  /-- The prior over initial states is finitely supported. -/
  initialFinite : setup.FiniteInitialLaw
  /-- The leak rule branches finitely. -/
  leaksFinite : leaks.FiniteSupport

attribute [instance] SourceServiceSpec.initialFinite SourceServiceSpec.leaksFinite

variable [Fintype Player]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

abbrev menu := sourceServiceMenu service.setup service.leaks service.bounds service.rosters

abbrev planLength : Nat := (rosterPlan service.setup service.rosters).length

abbrev scheduler := rosterScheduler service.setup service.leaks service.rosters service.network

/-- The source information model of the service's program, with every binding
value admitted. -/
abbrev sourceModel := service.setup.informationModel
  (CommitmentInterface.values service.setup.program)

/-- The native information model of the retained service. -/
abbrev model := service.menu.information (initialLaw service.setup) service.planLength
  service.scheduler

/-- The horizon of the standard native continuation comparisons. -/
abbrev fuel : Nat := 2 * service.planLength + 1

/-- The typed source terminal state read from a native history. -/
abbrev readout (final : (service.menu.protocol (initialLaw service.setup) service.planLength
    service.scheduler).History) :
    Option (State L service.setup.program.terminalCtx) :=
  sourceReadout service.setup service.leaks final.state

end SourceServiceSpec

end Vegas
