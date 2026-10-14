/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedCountedLog
import Vegas.Pending.ReactiveLocalSeedExhaustionRun

/-! # Raw local logs along actual surviving ready intervals

A local resolution cannot occur on an execution path where the selected
event survives. Actual query counters and owner recall determine the
remaining activation and closed-clock entries.
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

/-- A surviving actual dispatch appends no resolution entry. -/
theorem dispatch_log_unresolved
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (execution next : (app).Execution) (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (valid : execution.application.Invariant inputs) (genuine : controller.domain execution)
    (unfinished : event ∉ next.application.config.cut.completed)
    (unresolved : ∀ entry ∈ memory.log,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (reached : next ∈ ((app).dispatch players
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).1 execution).support) :
    ∀ entry ∈ (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log,
        entry.reply = .activation ∨ entry.reply = .exhausted := by
  classical
  generalize stepEq : controller.step remainder memory execution.environmentRecall
    (execution.observeEnvironment app) = result at reached ⊢
  dsimp only [step] at stepEq
  split_ifs at stepEq with ready closed polled
  · rw [← stepEq]
    exact unresolved
  · rw [← stepEq] at reached ⊢
    let query : CurrentSeedQuery graph :=
      ⟨runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app),
        memory.activationIndex⟩
    change ∀ entry ∈ (finishReply owner memory _ query
      (controller.reply memory.localSeed query)).2.log, _
    rw [finishReply_log]
    intro entry member
    rcases List.mem_append.mp member with earlier | last
    · exact unresolved entry earlier
    · have entryEq : entry = ⟨query, controller.reply memory.localSeed query⟩ := by
        simpa only [List.mem_singleton] using last
      subst entry
      cases answer : controller.reply memory.localSeed query with
      | activation => exact Or.inl rfl
      | exhausted => exact Or.inr rfl
      | resolution command =>
          exfalso
          apply unfinished
          apply controller.resolution_dispatch_completes inputs players memory.localSeed query
            execution next command valid genuine rfl ready answer
          simpa only [query, answer, finishReply] using reached
  · rw [← stepEq]
    exact unresolved
  · rw [← stepEq]
    exact unresolved

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

/-- All raw-log invariants follow the actual surviving path. Domain preservation
is required only while the selected ready event survives the dispatch. -/
theorem runJoint_survivorLog
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy) (entered : Nat)
    (preserves : ∀ execution memory next, controller.domain execution →
      execution.application.Invariant inputs →
      execution.application.activatedAt event = some entered →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next)
    (count : Nat) (execution : (app).Execution)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support)
    (genuine : controller.domain execution) (valid : execution.application.Invariant inputs)
    (activated : execution.application.activatedAt event = some entered)
    (recalled : execution.InputRecall app)
    (counted : CountedQueryLog memory.log)
    (unresolved : ∀ entry ∈ memory.log,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (positiveMatch : positiveQueries memory.log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexMatch : memory.activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (clocks : exhaustedClocks memory.log =
      List.range (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ++
      if memory.closedAt = some (runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed then
        [(runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed] else []) :
    CountedQueryLog after.log ∧
      (∀ entry ∈ after.log, entry.reply = .activation ∨ entry.reply = .exhausted) ∧
      positiveQueries after.log = runtime.ownerActivationQueries leaks event (next.recall owner) ∧
      after.activationIndex = runtime.readyActivationCount leaks event (next.recall owner) ∧
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
      exact ⟨counted, unresolved, positiveMatch, indexMatch, clocks⟩
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have first := runtime.reactive_dispatch_progress leaks inputs players execution middle _
        valid moved
      obtain ⟨ticks, rest⟩ := controller.runJoint_progress localLaw remainderLaw remainder inputs
        players count middle _ next after first.invariant later
      have middleUnfinished : event ∉ middle.application.config.cut.completed :=
        fun completed => unfinished (rest.completed completed)
      have indexed : memory.activationIndex = (positiveQueries memory.log).length := by
        rw [positiveMatch, runtime.ownerActivationQueries_length]
        exact indexMatch
      have middleCounted := controller.step_countedLog remainder memory execution.environmentRecall
        (execution.observeEnvironment app) counted indexed clocks
      have middleUnresolved := controller.dispatch_log_unresolved remainder inputs players execution
        middle memory valid genuine middleUnfinished unresolved moved
      have matched := controller.dispatch_ownerLog remainder memory execution middle players genuine
        recalled positiveMatch indexMatch moved
      have middleClocks := controller.dispatch_exhaustionRange remainder inputs players execution
        middle memory entered valid activated middleUnfinished genuine clocks moved
      exact ih middle _ later
        (preserves execution memory middle genuine valid activated moved middleUnfinished)
        first.invariant (first.activated event entered activated middleUnfinished)
        (dispatch_inputRecall players execution middle _ recalled moved)
        middleCounted middleUnresolved matched.1 matched.2 middleClocks

/-- An initially ready event has no hidden resolution entries on any supported
surviving path, and every raw query is counted from actual owner observations. -/
theorem runJoint_ready_initial_survivorLog
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (state : State graph) (localSeed : LocalSeed) (remainderSeed : RestSeed)
    (preserves : ∀ execution memory next, controller.domain execution →
      execution.application.Invariant inputs →
      execution.application.activatedAt event = some state.clock →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next)
    (count : Nat) (next : (app).Execution)
    (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (valid : state.Invariant inputs) (activated : state.activatedAt event = some state.clock)
    (genuine : controller.domain (ReactiveApplication.Execution.initial app state))
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        (ReactiveApplication.Execution.initial app state)
          (initialMemory localSeed remainderSeed)).support) :
    CountedQueryLog after.log ∧
      (∀ entry ∈ after.log, entry.reply = .activation ∨ entry.reply = .exhausted) ∧
      positiveQueries after.log = runtime.ownerActivationQueries leaks event (next.recall owner) ∧
      after.activationIndex = runtime.readyActivationCount leaks event (next.recall owner) ∧
      exhaustedClocks after.log =
        List.range (runtime.environmentSeedInput leaks owner event
          (next.observeEnvironment app)).elapsed ++
        if after.closedAt = some (runtime.environmentSeedInput leaks owner event
            (next.observeEnvironment app)).elapsed then
          [(runtime.environmentSeedInput leaks owner event
            (next.observeEnvironment app)).elapsed] else [] := by
  classical
  apply controller.runJoint_survivorLog localLaw remainderLaw remainder inputs players state.clock
    preserves count (ReactiveApplication.Execution.initial app state)
      (initialMemory localSeed remainderSeed) next after unfinished reached genuine valid activated
      ((app).initial_inputRecall state) CountedQueryLog.empty
  · simp [initialMemory]
  · rfl
  · rfl
  · change [] = List.range (state.clock - (state.activatedAt event).getD state.clock) ++
      if (none : Option Nat) = some (state.clock - (state.activatedAt event).getD state.clock) then
        [state.clock - (state.activatedAt event).getD state.clock] else []
    rw [activated]
    simp

end Vegas.EventGraphRuntime.LocalSeedController
