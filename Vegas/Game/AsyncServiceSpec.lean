/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceLocalComparison
import Vegas.Game.ServiceRosterAsync

/-! # Full-source services under an asynchronous scheduler

`Vegas.AsyncServiceSpec` is the full-source native service with an arbitrary
public scheduler in place of the roster calendar: the program setup, passive
observation rule and message bounds with the compiler's side conditions on
them, a horizon, and a scheduler satisfying the asynchronous contract with
per-event reaction bounds `delay` and inclusion bounds `bound` that leave room
before every deadline. It has no rosters and no activation opportunities: the
contract's opportunity clause replaces them.

The fixed roster calendar is one instance (`Vegas.SourceServiceSpec.toAsync`),
with the plan length as horizon, reaction bound `event.val` and inclusion
bound zero (`Vegas.rosterScheduler_asyncContract`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

/-- The full-source native service under an asynchronous scheduler: the
program setup, passive observation rule and message bounds, with the
compiler's side conditions on them, and a scheduler satisfying the
asynchronous contract up to a fixed horizon, with bounds that fit every
deadline. -/
structure AsyncServiceSpec (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] where
  setup : Setup (Player := Player) (L := L)
  leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))
  bounds : MessageBounds (graph setup)
  /-- Every binding value the source can choose has a native message form. -/
  values : bounds.CoversBindingValues
  /-- Every supported initial binding table fits the candidate catalogue. -/
  initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state
  /-- The candidate catalogue has a slot for every event. -/
  capacity : (graph setup).order.eventCount ≤ bounds.candidateCount
  /-- The number of scheduler rounds. -/
  horizon : Nat
  /-- The public scheduler: activations, inclusions, clock, sampling and expiry. -/
  scheduler : (application setup leaks).Scheduler
  /-- Per-event reaction bound: slots before the owner's first activation. -/
  delay : (graph setup).EventId → Nat
  /-- Per-event inclusion bound for an owner's sole packet. -/
  bound : (graph setup).EventId → Nat
  contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay bound
  /-- Every owned event's reaction and inclusion fit before its deadline. -/
  timely : AsyncTimely (runtime setup) delay bound
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
    (application service.setup service.leaks).FiniteNature (initialLaw service.setup)
      service.scheduler where
  initial_finite := by
    rw [initialLaw, PMF.support_map]
    exact service.setup.initialLaw_support_finite.image _
  scheduler_finite := service.schedulerFinite

/-- The scheduler completes every event by the horizon. -/
theorem completes : CompletesPlay (runtime service.setup) service.leaks
    (initialLaw service.setup) service.horizon service.scheduler :=
  service.contract.completes

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

end Vegas

-- OPEN OBLIGATION: Asynchronous sequential-equilibrium preservation
-- Prove every source sequential equilibrium has a bounded raw-runtime
-- equilibrium under any AsyncServiceSpec, preserving the joint source outcome
-- and realized settlement law. Retained slot invariants, prescribed policy
-- admission after misses and prescribed continuation bounds are checked.
-- The candidate owner-local risk menu, actual post-miss rationality and a
-- localized restriction-extension theorem are checked; their source embedding
-- and runtime comparison premises remain open.
-- Exact first-turn play records protected binding calls, keeps opportunity recall
-- clear and excludes all owned public binding misses against arbitrary foreign
-- raw policies. These operational results do not establish zero traffic charge
-- or the strategic source embedding.
-- The source extension supplying play at first unprotected binding opportunities,
-- after misses and after unprotected attempts,
-- joint beliefs with traffic observations, local incentives and general
-- continuation repair remain to be proved.
-- The fixed-calendar SourceServiceSpec capstone does not discharge this edge.
