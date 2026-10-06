/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceLocalComparison
import Vegas.Game.ServiceRosterAsync

/-! # Full-source services under an asynchronous scheduler

`Vegas.AsyncServiceSpec` is the full-source native service with an arbitrary
public scheduler in place of the roster calendar: the program setup, the
dependency mode of its event graph and a configured deadline duration per
event, passive observation rule and message bounds with the compiler's side
conditions on them, a horizon, and a scheduler satisfying the asynchronous
contract with per-event reaction bounds `delay` and inclusion bounds `bound`
that leave room before every configured deadline. It has no rosters and no
activation opportunities: the contract's opportunity clause replaces them.

The fixed roster calendar is one instance (`Vegas.SourceServiceSpec.toAsync`),
on the sequential graph with rank deadlines (`Vegas.RankSequential`), with the
plan length as horizon, reaction bound `event.val` and inclusion bound zero
(`Vegas.rosterScheduler_asyncContract`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

/-- The full-source native service under an asynchronous scheduler: the
program setup, the dependency mode and configured deadlines of its runtime,
passive observation rule and message bounds, with the compiler's side
conditions on them, and a scheduler satisfying the asynchronous contract up to
a fixed horizon, with bounds that fit every configured deadline. -/
structure AsyncServiceSpec (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] where
  setup : Setup (Player := Player) (L := L)
  /-- The dependency mode of the compiled event graph. -/
  mode : EventGraph.ExecutionMode
  /-- The configured deadline duration of each event, counted by the runtime
  from the clock at which the event became ready. -/
  deadline : (serviceGraph setup mode).EventId → Nat
  leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))
  bounds : MessageBounds (serviceGraph setup mode)
  /-- Every binding value the source can choose has a native message form. -/
  values : bounds.CoversBindingValues
  /-- Every supported initial binding table fits the candidate catalogue. -/
  initialValues : ∀ state ∈ (serviceInitialLaw setup mode).support, bounds.CandidateValues state
  /-- The candidate catalogue has a slot for every event. -/
  capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount
  /-- The number of scheduler rounds. -/
  horizon : Nat
  /-- The public scheduler: activations, inclusions, clock, sampling and expiry. -/
  scheduler : (serviceApplication setup mode deadline leaks).Scheduler
  /-- Per-event reaction bound: slots before the owner's first activation. -/
  delay : (serviceGraph setup mode).EventId → Nat
  /-- Per-event inclusion bound for an owner's sole packet. -/
  bound : (serviceGraph setup mode).EventId → Nat
  contract : AsyncContract (serviceRuntime setup mode deadline) leaks (serviceInitialLaw setup mode)
    horizon scheduler delay bound
  /-- Every owned event's reaction and inclusion fit before its configured
  deadline. -/
  timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound
  /-- The prior over initial states is finitely supported. -/
  initialFinite : setup.FiniteInitialLaw
  /-- The leak rule branches finitely. -/
  leaksFinite : leaks.FiniteSupport
  /-- The scheduler branches finitely. -/
  schedulerFinite : ∀ past view, (scheduler past view).support.Finite

attribute [instance] AsyncServiceSpec.initialFinite AsyncServiceSpec.leaksFinite

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace AsyncServiceSpec

variable (service : AsyncServiceSpec Player L)

/-- All of the service's nature branches finitely: the prior, the leak rule and
the scheduler. -/
instance finiteNature :
    (serviceApplication service.setup service.mode service.deadline service.leaks).FiniteNature
      (serviceInitialLaw service.setup service.mode) service.scheduler where
  initial_finite := serviceInitialLaw_support_finite service.setup service.mode
  scheduler_finite := service.schedulerFinite

/-- The scheduler completes every event by the horizon. -/
theorem completes : CompletesPlay (serviceRuntime service.setup service.mode service.deadline)
    service.leaks (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler :=
  service.contract.completes

/-- The service runs the sequential dependency mode with rank deadlines. -/
abbrev RankSequential : Prop := Vegas.RankSequential service.setup service.mode service.deadline

end AsyncServiceSpec

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
  mode := .sequential
  deadline := rankDeadline service.setup .sequential
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

/-- The calendar instance runs the sequential mode with rank deadlines. -/
theorem toAsync_rankSequential : service.toAsync.RankSequential := ⟨rfl, rfl⟩

@[simp] theorem toAsync_horizon : service.toAsync.horizon = service.planLength := rfl

@[simp] theorem toAsync_scheduler : service.toAsync.scheduler = service.scheduler := rfl

end SourceServiceSpec

end Vegas
