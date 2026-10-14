/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedOwnerRecall

/-! # Actual positive query-log transitions

The private log's activation projection records exactly the actual owner
decisions while its event is ready, with no bound on activations per clock.
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

/-- Extract the actual positive local queries, retaining order and repeated clocks. -/
def positiveQueries (log : List (LocalSeedEntry graph (app).Command)) :
    List (CurrentSeedQuery graph) := log.filterMap fun entry =>
  match entry.reply with
  | .activation => some entry.query
  | _ => none

open Classical in
/-- A positive private query appears precisely when the real next command
activates the selected owner at its ready event. -/
theorem step_positiveQueries
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (execution : (app).Execution)
    (genuine : controller.domain execution) :
    positiveQueries (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log =
      positiveQueries memory.log ++
        if (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 = .activate owner ∧
            execution.application.publicView.EventReady event then
          [⟨runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app),
            memory.activationIndex⟩] else [] := by
  classical
  generalize stepEq : controller.step remainder memory execution.environmentRecall
    (execution.observeEnvironment app) = result
  dsimp only [step] at stepEq
  split_ifs at stepEq with ready closed polled
  · rw [← stepEq]
    have different := (remainder.safe memory.remainderSeed execution.environmentRecall
      (execution.observeEnvironment app)).1 ready
    simp [different]
  · rw [← stepEq]
    let query : CurrentSeedQuery graph :=
      ⟨runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app),
        memory.activationIndex⟩
    change positiveQueries (finishReply owner memory _ query
      (controller.reply memory.localSeed query)).2.log =
      positiveQueries memory.log ++
        if (finishReply owner memory _ query (controller.reply memory.localSeed query)).1 =
            .activate owner ∧ execution.application.publicView.EventReady event then
          [query] else []
    change execution.application.publicView.EventReady event at ready
    cases answerEq : controller.reply memory.localSeed query with
    | activation => simp [finishReply, positiveQueries, ready]
    | resolution command =>
        have resolves := controller.resolves memory.localSeed query execution command genuine
          rfl ready (controller.service_of_resolution memory.localSeed query command answerEq)
        have different : command ≠ .activate owner := by
          intro same
          simpa only [same] using resolves.1
        simp [finishReply, positiveQueries, different]
    | exhausted =>
        have different := (remainder.safe memory.remainderSeed execution.environmentRecall
          (execution.observeEnvironment app)).1 ready
        simp [finishReply, positiveQueries, different]
  · rw [← stepEq]
    have different := (remainder.safe memory.remainderSeed execution.environmentRecall
      (execution.observeEnvironment app)).1 ready
    simp [different]
  · rw [← stepEq]
    change ¬ execution.application.publicView.EventReady event at ready
    simp [ready]

/-- Bookkeeping counts every positive query, including silent repeated activations. -/
theorem step_index_eq_positive_length
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (indexed : memory.activationIndex = (positiveQueries memory.log).length) :
    (controller.step remainder memory past view).2.activationIndex =
      (positiveQueries (controller.step remainder memory past view).2.log).length := by
  classical
  dsimp only [step]
  split_ifs
  · exact indexed
  · cases controller.reply memory.localSeed
      ⟨runtime.environmentSeedInput leaks owner event view, memory.activationIndex⟩ <;>
        simp [finishReply, positiveQueries, indexed]
  · exact indexed
  · exact indexed

/-- One supported real dispatch preserves reconstruction of all positive
queries and their indices from the owner's full actual recall. -/
theorem dispatch_ownerLog
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (execution next : (app).Execution)
    (players : Player → (app).Policy) (genuine : controller.domain execution)
    (recalled : execution.InputRecall app)
    (positiveMatch : positiveQueries memory.log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexMatch : memory.activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (reached : next ∈ ((app).dispatch players
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).1 execution).support) :
    positiveQueries (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).2.log =
      runtime.ownerActivationQueries leaks event (next.recall owner) ∧
    (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).2.activationIndex =
      runtime.readyActivationCount leaks event (next.recall owner) := by
  have matched : positiveQueries (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).2.log =
      runtime.ownerActivationQueries leaks event (next.recall owner) := by
    rw [controller.step_positiveQueries remainder memory execution genuine, positiveMatch,
      indexMatch, runtime.seedInput_eq_of_inputRecall leaks execution recalled owner event]
    exact (runtime.dispatch_ownerActivationQueries leaks players execution next _ owner event
      reached).symm
  refine ⟨matched, ?_⟩
  have indexed : memory.activationIndex = (positiveQueries memory.log).length := by
    rw [positiveMatch, runtime.ownerActivationQueries_length]
    exact indexMatch
  rw [controller.step_index_eq_positive_length remainder memory execution.environmentRecall
    (execution.observeEnvironment app) indexed, matched, runtime.ownerActivationQueries_length]

end Vegas.EventGraphRuntime.LocalSeedController
