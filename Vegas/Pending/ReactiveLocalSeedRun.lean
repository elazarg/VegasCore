/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedScheduler

/-! # Actual execution-prefix splicing for locally queried seeds

Replacing a local seed by one agreeing with the actual query log preserves
the concrete dispatch history and all nonseed private memory.
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

variable (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
  (remainder : SeedRemainderController runtime leaks RestSeed owner event)

/-- One concrete round emits the deterministic local-controller command and
then uses the unchanged actual player/application dispatch kernel. -/
theorem runJoint_succ (players : Player → (app).Policy) (count : Nat)
    (execution : (app).Execution) (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) :
    (controller.implementation localLaw remainderLaw remainder).runJoint players (count + 1)
        execution memory =
      ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).bind fun next =>
        (controller.implementation localLaw remainderLaw remainder).runJoint players count next
          (controller.step remainder memory execution.environmentRecall
            (execution.observeEnvironment app)).2 := by
  simp only [ReactiveApplication.SchedulerImplementation.runJoint, implementation,
    PMF.pure_bind]

/-- Every supported actual execution prefix retains all previous local queries. -/
theorem runJoint_log_prefix (players : Player → (app).Policy) (count : Nat)
    (execution : (app).Execution) (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) : memory.log <+: after.log := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact List.prefix_refl _
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact (controller.step_log_prefix remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).trans (ih middle _ later)

/-- An alternative local seed consistent with every actual query can replay
the same complete execution prefix, retaining the remainder seed and log. -/
theorem runJoint_replaceLocal_support (players : Player → (app).Policy) (count : Nat)
    (execution : (app).Execution) (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support)
    (seed : LocalSeed)
    (agrees : ∀ entry ∈ after.log, controller.reply seed entry.query = entry.reply) :
    (next, after.replaceLocal seed) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution (memory.replaceLocal seed)).support := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | succ count ih =>
      rw [controller.runJoint_succ] at reached ⊢
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have logPrefix := controller.runJoint_log_prefix localLaw remainderLaw remainder
        players count middle _ next after later
      have splice := controller.step_replaceLocal_of_log remainder memory seed
        execution.environmentRecall (execution.observeEnvironment app)
        (fun entry member => agrees entry (logPrefix.subset member))
      rw [splice]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨middle, moved,
        ih middle _ later⟩

end Vegas.EventGraphRuntime.LocalSeedController
