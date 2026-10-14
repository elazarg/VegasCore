/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedExhaustion
import Vegas.Pending.ReactiveLocalSeedPositiveLog

/-! # Actual local query counters

A recorded query reads exactly the number of previous exhausted clocks and
positive activations. The controller establishes these counters when it
appends a query, without assuming any posterior property.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => runtime.reactiveApplication leaks

/-- Each raw query records its actual two preceding local transcript counters. -/
inductive CountedQueryLog : List (LocalSeedEntry graph (app).Command) → Prop where
  | empty : CountedQueryLog []
  | append {past} (recorded : CountedQueryLog past)
      (entry : LocalSeedEntry graph (app).Command)
      (clock : entry.query.input.elapsed = (exhaustedClocks past).length)
      (index : entry.query.activationIndex = (positiveQueries past).length) :
      CountedQueryLog (past ++ [entry])

variable {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

/-- The concrete controller appends a correctly counted query whenever its
actual clock and activation invariants permit a local poll. -/
theorem step_countedLog
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (recorded : CountedQueryLog memory.log)
    (indexed : memory.activationIndex = (positiveQueries memory.log).length)
    (clocks : exhaustedClocks memory.log =
      List.range (runtime.environmentSeedInput leaks owner event view).elapsed ++
        if memory.closedAt = some (runtime.environmentSeedInput leaks owner event view).elapsed
          then [(runtime.environmentSeedInput leaks owner event view).elapsed] else []) :
    CountedQueryLog (controller.step remainder memory past view).2.log := by
  classical
  dsimp only [step]
  split_ifs with ready closed polled
  · exact recorded
  · rw [finishReply_log]
    refine CountedQueryLog.append recorded _ ?_ indexed
    change (runtime.environmentSeedInput leaks owner event view).elapsed =
      (exhaustedClocks memory.log).length
    rw [clocks, ite_eq_right closed, List.append_nil, List.length_range]
  · exact recorded
  · exact recorded

/-- An actual local resolution reply completes its selected event through
the true environment and player dispatch kernels. -/
theorem resolution_dispatch_completes
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (seed : LocalSeed) (query : CurrentSeedQuery graph)
    (execution next : (app).Execution) (command : (app).Command)
    (valid : execution.application.Invariant inputs) (genuine : controller.domain execution)
    (inputEq : runtime.environmentSeedInput leaks owner event
      (execution.observeEnvironment app) = query.input)
    (ready : execution.application.publicView.EventReady event)
    (answer : controller.reply seed query = .resolution command)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    event ∈ next.application.config.cut.completed := by
  obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have before := runtime.reactive_environment_progress leaks inputs execution middle command
    valid moved
  have completed := controller.resolution_completes seed query execution middle command genuine
    inputEq ready answer moved
  have after := runtime.reactive_resume_progress leaks inputs players _ middle next
    before.invariant responded
  exact after.completed completed

end Vegas.EventGraphRuntime.LocalSeedController
