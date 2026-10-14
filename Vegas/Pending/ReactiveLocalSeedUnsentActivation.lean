/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedLogRecovery
import Vegas.Pending.ReactiveLocalSeedClock

/-! # The raw local log at an unsent owner activation

Before the selected event emits a packet, a genuine owner activation fixes
the entire raw log from its positive owner queries and current elapsed clock.
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

/-- The private raw log at a genuine unsent owner activation has a unique
activation/exhaustion encoding, whose signature is actual owner information. -/
theorem activation_unsent_signature
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (execution : (app).Execution)
    (genuine : controller.domain execution) (recalled : execution.InputRecall app)
    (ready : execution.application.publicView.EventReady event)
    (activated : (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).1 = .activate owner)
    (counted : CountedQueryLog memory.log)
    (unresolved : ∀ entry ∈ memory.log,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (unsent : ∀ entry ∈ memory.log, entry.query.input.emitted = [])
    (empty : (runtime.ownerSeedInput leaks event (execution.recall owner)
      (execution.observe app owner)).emitted = [])
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
    ∃ word : List Bool,
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).2.log =
          encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word ∧
      positiveQueries (encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word) =
        runtime.ownerActivationQueries leaks event (execution.recall owner) ++
          [⟨runtime.ownerSeedInput leaks event (execution.recall owner)
            (execution.observe app owner),
              runtime.readyActivationCount leaks event (execution.recall owner)⟩] ∧
      (exhaustedClocks
        (encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word)).length =
          (runtime.ownerSeedInput leaks event (execution.recall owner)
            (execution.observe app owner)).elapsed := by
  classical
  have indexed : memory.activationIndex = (positiveQueries memory.log).length := by
    rw [positiveMatch, runtime.ownerActivationQueries_length]
    exact indexMatch
  have newCounted := controller.step_countedLog remainder memory execution.environmentRecall
    (execution.observeEnvironment app) counted indexed clocks
  have newLog := controller.activation_log remainder memory execution genuine recalled ready
    activated
  have notClosed := controller.activation_not_closed remainder memory execution ready activated
  rw [ite_eq_right notClosed, List.append_nil] at clocks
  let query : CurrentSeedQuery graph :=
    ⟨runtime.ownerSeedInput leaks event (execution.recall owner)
      (execution.observe app owner), memory.activationIndex⟩
  have nextUnsent : ∀ entry ∈ (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log, entry.query.input.emitted = [] := by
    rw [newLog]
    intro entry member
    rcases List.mem_append.mp member with prior | last
    · exact unsent entry prior
    · have same : entry = ⟨query, .activation⟩ := by simpa only [List.mem_singleton] using last
      subst entry
      exact empty
  have nextUnresolved : ∀ entry ∈ (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log,
        entry.reply = .activation ∨ entry.reply = .exhausted := by
    rw [newLog]
    intro entry member
    rcases List.mem_append.mp member with prior | last
    · exact unresolved entry prior
    · have same : entry = ⟨query, .activation⟩ := by simpa only [List.mem_singleton] using last
      subst entry
      exact Or.inl rfl
  obtain ⟨word, wordEq⟩ := newCounted.encode_unsent nextUnsent nextUnresolved
  refine ⟨word, wordEq, ?_, ?_⟩
  · rw [← wordEq, newLog]
    simp only [positiveQueries, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil]
    change positiveQueries memory.log ++ [query] = _
    rw [positiveMatch]
    simp only [query, indexMatch]
  · rw [← wordEq, newLog]
    change (exhaustedClocks (memory.log ++ [⟨query, .activation⟩])).length = _
    simp only [exhaustedClocks, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
    change (exhaustedClocks memory.log).length = _
    rw [clocks, List.length_range,
      runtime.seedInput_eq_of_inputRecall leaks execution recalled owner event]

end Vegas.EventGraphRuntime.LocalSeedController
