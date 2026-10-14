/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedPositiveLog
import Vegas.Pending.ReactiveLocalSeedReplay

/-! # Positive local query recovery along complete actual runs

An operationally invariant service domain suffices to reconstruct every
positive local query from the owner's real recall, for arbitrary policies
and arbitrarily many same-clock activations.
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

private theorem dispatch_inputRecall (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command)
    (recalled : execution.InputRecall app)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    next.InputRecall app := by
  obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have middleRecall := (app).environment_inputRecall execution middle command recalled moved
  cases acting : command.actor? app with
  | none =>
      simp only [acting, ReactiveApplication.resume] at responded
      cases (PMF.mem_support_pure_iff _ _).mp responded
      exact middleRecall
  | some actor =>
      simp only [acting, ReactiveApplication.resume, ReactiveApplication.invoke] at responded
      obtain ⟨action, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp responded
      exact (app).respond_inputRecall middle actor action middleRecall

/-- Actual run-prefix positive-query recovery, conditional only on preservation
of the genuine operational service domain and its ordinary induction invariants. -/
theorem runJoint_ownerLog
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (players : Player → (app).Policy)
    (preserves : ∀ execution memory next, controller.domain execution →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support → controller.domain next)
    (count : Nat) (execution : (app).Execution)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (next : (app).Execution)
    (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support)
    (genuine : controller.domain execution) (recalled : execution.InputRecall app)
    (positiveMatch : positiveQueries memory.log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexMatch : memory.activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner)) :
    positiveQueries after.log = runtime.ownerActivationQueries leaks event (next.recall owner) ∧
      after.activationIndex = runtime.readyActivationCount leaks event (next.recall owner) := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨positiveMatch, indexMatch⟩
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have matched := controller.dispatch_ownerLog remainder memory execution middle players
        genuine recalled positiveMatch indexMatch moved
      exact ih middle _ later (preserves execution memory middle genuine moved)
        (dispatch_inputRecall players execution middle _ recalled moved) matched.1 matched.2

/-- Initialized actual runs expose all positive local queries through the
owner's real recall; no posterior or observation-factorization premise is used. -/
theorem runJoint_initial_ownerLog
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (players : Player → (app).Policy)
    (preserves : ∀ execution memory next, controller.domain execution →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support → controller.domain next)
    (count : Nat) (state : State graph) (localSeed : LocalSeed) (remainderSeed : RestSeed)
    (genuine : controller.domain (ReactiveApplication.Execution.initial app state))
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        (ReactiveApplication.Execution.initial app state)
          (initialMemory localSeed remainderSeed)).support) :
    positiveQueries after.log = runtime.ownerActivationQueries leaks event (next.recall owner) ∧
      after.activationIndex = runtime.readyActivationCount leaks event (next.recall owner) :=
  controller.runJoint_ownerLog localLaw remainderLaw remainder players preserves count
    (ReactiveApplication.Execution.initial app state) (initialMemory localSeed remainderSeed)
    next after reached genuine ((app).initial_inputRecall state) rfl rfl

end Vegas.EventGraphRuntime.LocalSeedController
