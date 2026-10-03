/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceSpec
import Vegas.Game.AsyncServiceDeposit
import Vegas.Game.SourceServiceLocalComparison
import Vegas.Game.ServiceRosterAsync
import Vegas.Game.ServicePayoffBounds

/-! # The retained source calendar as an asynchronous service

The concrete roster service satisfies the generic asynchronous contract with
its plan length as horizon, reaction bound equal to event rank, and inclusion
bound zero. The instance preserves the concrete scheduler and its deposit.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- **The calendar instance.** The fixed roster service is an asynchronous
service with the plan length as horizon, reaction bound `event.val` and
inclusion bound zero. -/
def toAsync : AsyncServiceSpec Player L where
  setup := service.setup
  leaks := service.leaks
  bounds := service.bounds
  values := service.values
  initialValues := service.initialValues
  capacity := service.capacity
  horizon := service.planLength
  scheduler := service.scheduler
  delay := fun event => event.val
  bound := fun _ => 0
  contract := rosterScheduler_asyncContract service.setup service.leaks service.rosters
    service.network service.opportunities
  timely := rosterScheduler_asyncTimely service.setup
  initialFinite := service.initialFinite
  leaksFinite := service.leaksFinite
  schedulerFinite := ReactiveApplication.FiniteNature.scheduler_finite
    (initial := initialLaw service.setup)

@[simp] theorem toAsync_horizon : service.toAsync.horizon = service.planLength := rfl

@[simp] theorem toAsync_scheduler : service.toAsync.scheduler = service.scheduler := rfl

end SourceServiceSpec

variable [Fintype Player]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler] in
/-- On the roster calendar the deposit is the calendar's deposit. -/
theorem rosterAuditDeposit_eq_async [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) [network.FiniteSupport]
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) :
    rosterAuditDeposit setup leaks bounds rosters network base probability who =
      asyncAuditDeposit setup leaks bounds (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) base probability who :=
  rfl

/-- On the calendar instance the service's deposit is the roster deposit. -/
theorem SourceServiceSpec.toAsync_auditDeposit (service : SourceServiceSpec Player L)
    (base : (application service.setup service.leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) :
    service.toAsync.auditDeposit base probability who =
      rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
        service.network base probability who :=
  rfl

end Vegas
