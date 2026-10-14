/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedClock
import Vegas.Pending.ReactiveServiceProgress

/-! # Recorded local exhaustion clocks along actual service

Memoized exhaustion records are added once at the current relative clock.
Actual survivor progress preserves the event's readiness timestamp, so elapsed
time advances exactly with the application's genuine clock ticks.
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

/-- Extract the actual local exhaustion clocks in their recorded order. -/
def exhaustedClocks (log : List (LocalSeedEntry graph (app).Command)) : List Nat :=
  log.filterMap fun entry => match entry.reply with
    | .exhausted => some entry.query.input.elapsed
    | _ => none

/-- At an already closed clock the private bookkeeping is unchanged. -/
theorem step_preserves_closed
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (closed : memory.closedAt = some
      (runtime.environmentSeedInput leaks owner event view).elapsed) :
    (controller.step remainder memory past view).2 = memory := by
  classical
  simp only [step, closed, ↓reduceIte, ite_self]

/-- A step appends an exhaustion precisely when it newly closes its current clock. -/
theorem step_exhaustedClocks
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    exhaustedClocks (controller.step remainder memory past view).2.log =
      exhaustedClocks memory.log ++
        if memory.closedAt ≠ some (runtime.environmentSeedInput leaks owner event view).elapsed ∧
            (controller.step remainder memory past view).2.closedAt =
              some (runtime.environmentSeedInput leaks owner event view).elapsed then
          [(runtime.environmentSeedInput leaks owner event view).elapsed] else [] := by
  classical
  generalize stepEq : controller.step remainder memory past view = result
  dsimp only [step] at stepEq
  split_ifs at stepEq with ready closed polled
  · rw [← stepEq]
    simp
  · rw [← stepEq]
    cases controller.reply memory.localSeed
      ⟨runtime.environmentSeedInput leaks owner event view, memory.activationIndex⟩ <;>
        simp [finishReply, exhaustedClocks, closed]
  · rw [← stepEq]
    simp
  · rw [← stepEq]
    simp

/-- Before dispatch changes the public clock, the recorded exhaustion range
is updated exactly with its current memoized closure flag. -/
theorem step_exhaustionRange
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (recorded : exhaustedClocks memory.log =
      List.range (runtime.environmentSeedInput leaks owner event view).elapsed ++
        if memory.closedAt = some (runtime.environmentSeedInput leaks owner event view).elapsed
          then [(runtime.environmentSeedInput leaks owner event view).elapsed] else []) :
    exhaustedClocks (controller.step remainder memory past view).2.log =
      List.range (runtime.environmentSeedInput leaks owner event view).elapsed ++
        if (controller.step remainder memory past view).2.closedAt =
            some (runtime.environmentSeedInput leaks owner event view).elapsed then
          [(runtime.environmentSeedInput leaks owner event view).elapsed] else [] := by
  classical
  rw [controller.step_exhaustedClocks, recorded]
  by_cases closed : memory.closedAt = some
      (runtime.environmentSeedInput leaks owner event view).elapsed
  · rw [controller.step_preserves_closed remainder memory past view closed]
    simp [closed]
  · simp [closed]

end Vegas.EventGraphRuntime.LocalSeedController

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A surviving actual event retains its readiness origin, and its elapsed
clock grows by the genuine runtime command's tick count. -/
theorem dispatch_seedElapsed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command) (owner : Player)
    (event : graph.EventId) (entered : Nat) (valid : execution.application.Invariant inputs)
    (activated : execution.application.activatedAt event = some entered)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support) :
    (runtime.environmentSeedInput leaks owner event
      (next.observeEnvironment (runtime.reactiveApplication leaks))).elapsed =
      (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment (runtime.reactiveApplication leaks))).elapsed +
          runtime.reactiveTicks leaks command := by
  have progress := runtime.reactive_dispatch_progress leaks inputs players execution next command
    valid reached
  have origin := progress.activated event entered activated unfinished
  have bound := valid.activated_le event entered activated
  change next.application.clock - (next.application.activatedAt event).getD
      next.application.clock = execution.application.clock -
        (execution.application.activatedAt event).getD execution.application.clock + _
  simp only [origin, activated, Option.getD_some, progress.clock]
  omega

end Vegas.EventGraphRuntime
