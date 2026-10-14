/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedReplay

/-! # Actual command transcript reconstruction for local seed runs

Supported concrete dispatch prefixes reconstruct their deterministic private
query log from the real environment inputs.
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

variable (remainder : SeedRemainderController runtime leaks RestSeed owner event)

/-- Every supported genuine run realizes its recorded command transcript and
its final log is exactly deterministic replay of those real inputs. -/
theorem runJoint_transcript (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (players : Player → (app).Policy) (count : Nat) (execution : (app).Execution)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (next : (app).Execution)
    (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) :
    ∃ suffix : List (app).EnvironmentEntry,
      next.environmentRecall = execution.environmentRecall ++ suffix ∧
      controller.followsFrom remainder memory execution.environmentRecall suffix ∧
      after = controller.replayFrom remainder memory execution.environmentRecall suffix := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨[], (List.append_nil _).symm, trivial, rfl⟩
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨suffix, recallEq, follows, replayed⟩ := ih middle _ later
      have recorded := (app).dispatch_environmentRecall players _ execution middle moved
      refine ⟨⟨execution.observeEnvironment app,
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1⟩ :: suffix, ?_, ?_, ?_⟩
      · rw [recallEq, recorded, List.append_assoc]
        rfl
      · refine ⟨rfl, ?_⟩
        simpa only [recorded] using follows
      · simpa only [replayFrom, ← recorded] using replayed

end Vegas.EventGraphRuntime.LocalSeedController
