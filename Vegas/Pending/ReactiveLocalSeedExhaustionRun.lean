/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedExhaustion
import Vegas.Pending.ReactiveLocalSeedReplay

/-! # Exhaustion clocks of surviving actual ready intervals

Concrete dispatch progress preserves a surviving event's readiness origin.
Each elapsed clock is exhausted exactly once before the next clock begins.
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

/-- Every supported private-controller run is actual cumulative service progress. -/
theorem runJoint_progress (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy) (count : Nat)
    (execution : (app).Execution) (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (valid : execution.application.Invariant inputs)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) :
    ∃ ticks, State.ServiceProgress inputs ticks execution.application next.application := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨0, State.ServiceProgress.refl valid⟩
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have first := runtime.reactive_dispatch_progress leaks inputs players execution middle _
        valid moved
      obtain ⟨ticks, rest⟩ := ih middle _ first.invariant later
      exact ⟨_, first.trans rest⟩

/-- One actual surviving ready-event dispatch preserves the exhaustion range
at its new relative clock, including arbitrarily many commands at one clock. -/
theorem dispatch_exhaustionRange
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (execution next : (app).Execution) (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (entered : Nat) (valid : execution.application.Invariant inputs)
    (activated : execution.application.activatedAt event = some entered)
    (unfinished : event ∉ next.application.config.cut.completed)
    (genuine : controller.domain execution)
    (recorded : exhaustedClocks memory.log =
      List.range (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ++
      if memory.closedAt = some (runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed then
        [(runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed] else [])
    (reached : next ∈ ((app).dispatch players
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).1 execution).support) :
    exhaustedClocks (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).2.log =
      List.range (runtime.environmentSeedInput leaks owner event
        (next.observeEnvironment app)).elapsed ++
      if (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).2.closedAt =
            some (runtime.environmentSeedInput leaks owner event
              (next.observeEnvironment app)).elapsed then
        [(runtime.environmentSeedInput leaks owner event
          (next.observeEnvironment app)).elapsed] else [] := by
  classical
  have localRange := controller.step_exhaustionRange remainder memory execution.environmentRecall
    (execution.observeEnvironment app) recorded
  have elapsedEq := runtime.dispatch_seedElapsed leaks inputs players execution next _ owner event
    entered valid activated unfinished reached
  have readyCut := ((valid.activated_iff event).mp (by simp [activated])).1
  have ready := (execution.application.publicView_eventReady event).mpr readyCut
  let command := (controller.step remainder memory execution.environmentRecall
    (execution.observeEnvironment app)).1
  by_cases advanced : command = .application .advanceClock
  · have ticks : runtime.reactiveTicks leaks command = 1 := by rw [advanced]; rfl
    change runtime.reactiveTicks leaks
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).1 = 1 at ticks
    have closed := controller.advance_closed remainder memory execution genuine ready advanced
    simp only [closed, ↓reduceIte] at localRange
    have different : some (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ≠
        some ((runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed + 1) := by simp
    simpa only [elapsedEq, ticks, closed, ite_eq_right different, List.append_nil,
      List.range_succ] using localRange
  · have ticks : runtime.reactiveTicks leaks command = 0 := by
      cases commandEq : command with
      | application operation =>
          cases operation with
          | advanceClock => exact False.elim (advanced commandEq)
          | executeSample other => rfl
          | expire other => rfl
      | activate actor => rfl
      | «include» id => rfl
      | wait => rfl
    change runtime.reactiveTicks leaks
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).1 = 0 at ticks
    simpa only [elapsedEq, ticks, Nat.add_zero] using localRange

/-- Every actual surviving ready interval records one exhaustion for each
closed relative clock, and at most one for its current clock. -/
theorem runJoint_exhaustionRange (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (preserves : ∀ execution memory next, controller.domain execution →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support → controller.domain next)
    (count : Nat) (execution : (app).Execution)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (next : (app).Execution)
    (after : LocalSeedMemory runtime leaks LocalSeed RestSeed) (entered : Nat)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support)
    (genuine : controller.domain execution) (valid : execution.application.Invariant inputs)
    (activated : execution.application.activatedAt event = some entered)
    (recorded : exhaustedClocks memory.log =
      List.range (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ++
      if memory.closedAt = some (runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed then
        [(runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed] else []) :
    exhaustedClocks after.log =
      List.range (runtime.environmentSeedInput leaks owner event
        (next.observeEnvironment app)).elapsed ++
      if after.closedAt = some (runtime.environmentSeedInput leaks owner event
          (next.observeEnvironment app)).elapsed then
        [(runtime.environmentSeedInput leaks owner event
          (next.observeEnvironment app)).elapsed] else [] := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact recorded
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have first := runtime.reactive_dispatch_progress leaks inputs players execution middle _
        valid moved
      obtain ⟨ticks, rest⟩ := controller.runJoint_progress localLaw remainderLaw remainder inputs
        players count middle _ next after first.invariant later
      have middleUnfinished : event ∉ middle.application.config.cut.completed :=
        fun completed => unfinished (rest.completed completed)
      have middleActivated := first.activated event entered activated middleUnfinished
      have middleRecorded := controller.dispatch_exhaustionRange remainder inputs players
        execution middle memory entered valid activated middleUnfinished genuine recorded moved
      exact ih middle _ later (preserves execution memory middle genuine moved) first.invariant
        middleActivated middleRecorded

/-- A concrete event ready at initialization records exactly its elapsed
closed clocks throughout every supported surviving run. -/
theorem runJoint_ready_initial_exhaustionRange
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (preserves : ∀ execution memory next, controller.domain execution →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support → controller.domain next)
    (count : Nat) (state : State graph) (localSeed : LocalSeed) (remainderSeed : RestSeed)
    (valid : state.Invariant inputs) (activated : state.activatedAt event = some state.clock)
    (genuine : controller.domain (ReactiveApplication.Execution.initial app state))
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        (ReactiveApplication.Execution.initial app state)
          (initialMemory localSeed remainderSeed)).support) :
    exhaustedClocks after.log =
      List.range (runtime.environmentSeedInput leaks owner event
        (next.observeEnvironment app)).elapsed ++
      if after.closedAt = some (runtime.environmentSeedInput leaks owner event
          (next.observeEnvironment app)).elapsed then
        [(runtime.environmentSeedInput leaks owner event
          (next.observeEnvironment app)).elapsed] else [] := by
  classical
  apply controller.runJoint_exhaustionRange localLaw remainderLaw remainder inputs players
    preserves count (ReactiveApplication.Execution.initial app state)
      (initialMemory localSeed remainderSeed) next after state.clock unfinished reached genuine
        valid activated
  change [] = List.range (state.clock - (state.activatedAt event).getD state.clock) ++
    if (none : Option Nat) = some (state.clock - (state.activatedAt event).getD state.clock) then
      [state.clock - (state.activatedAt event).getD state.clock] else []
  rw [activated]
  simp

end Vegas.EventGraphRuntime.LocalSeedController
