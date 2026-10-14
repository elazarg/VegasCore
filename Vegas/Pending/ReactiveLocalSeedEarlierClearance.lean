/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveReadyOwnerMiss
import Vegas.Pending.ReactiveLocalSeedReplay

/-! # Public binding clearance at actual earlier scheduler prefixes

Actual binding misses persist, so a final clear owner was clear at every
supported earlier local-controller prefix, even before its selected event
became ready.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Final public binding clearance transfers backwards along the actual run,
without a service domain, event ordering, or selected readiness premise. -/
theorem runJoint_unmissed_before
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (players : Player → (app).Policy) (count : Nat)
    (execution next : (app).Execution)
    (memory after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support)
    (unmissed : next.application.publicView.missedBindingBy owner = false) :
    execution.application.publicView.missedBindingBy owner = false := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact unmissed
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact runtime.unmissed_before_dispatch leaks players execution middle _ moved owner
        (ih middle _ later)

end Vegas.EventGraphRuntime.LocalSeedController
