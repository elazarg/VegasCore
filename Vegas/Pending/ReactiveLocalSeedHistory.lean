/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedRun
import Interaction.ReactiveTraceExtension

/-! # Actual menu histories of the local seed driver -/

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

/-- Every supported local-seed run extends an actual actor-free menu history.
The scheduler witness changes only to retain the realized commands; no service
domain or owner-clear condition is needed for this reachability statement. -/
theorem runJoint_trace
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (menu : (app).ResponseMenu) (initial : PMF (app).State)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (count horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (execution : (app).Execution)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) :
    ∃ extendedScheduler, Nonempty ((menu.protocol initial (horizon + count) extendedScheduler).Trace
      (some ⟨remaining, none, next⟩)) := by
  induction count generalizing horizon scheduler execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨scheduler, ⟨trace⟩⟩
  | succ count ih =>
      rw [controller.runJoint_succ localLaw remainderLaw remainder] at reached
      obtain ⟨middle, moved, suffix⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨extended, ⟨realized⟩⟩ := menu.trace_dispatch initial horizon scheduler remaining
        execution middle trace players covered _ moved
      obtain ⟨lastScheduler, finalTrace⟩ := ih (horizon + 1) extended middle _ realized suffix
      refine ⟨lastScheduler, ?_⟩
      have adjusted : (horizon + 1) + count = horizon + (count + 1) := by omega
      rwa [adjusted] at finalTrace

end Vegas.EventGraphRuntime.LocalSeedController
