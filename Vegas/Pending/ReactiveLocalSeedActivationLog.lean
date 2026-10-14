/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedEmissionPrefix
import Vegas.Pending.ReactiveLocalSeedCountedLog
import Vegas.Pending.ReactiveLocalSeedClock

/-! # Complete raw-log data at genuine owner activations

The owner reconstructs authored packet prefixes from recall at every local
activation index. Ready activation records therefore retain the full raw log
signature even when a packet has already been sent.
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

/-- Every raw log field needed for uniqueness is determined at a genuine
owner activation, including after the owner has transmitted its packet. -/
theorem activation_log_signature
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (execution : (app).Execution)
    (genuine : controller.domain execution) (recalled : execution.InputRecall app)
    (ready : execution.application.publicView.EventReady event)
    (activated : (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).1 = .activate owner)
    (counted : CountedQueryLog memory.log)
    (unresolved : ∀ entry ∈ memory.log,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (emitted : ∀ entry ∈ memory.log, entry.query.input.emitted =
      runtime.ownerEmissionsAtActivation leaks event (execution.recall owner)
        entry.query.activationIndex)
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
    CountedQueryLog (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log ∧
    (∀ entry ∈ (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).2.log,
      entry.reply = .activation ∨ entry.reply = .exhausted) ∧
    (∀ entry ∈ (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).2.log,
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (execution.recall owner) entry.query.activationIndex) ∧
    positiveQueries (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log =
        runtime.ownerActivationQueries leaks event (execution.recall owner) ++
          [⟨runtime.ownerSeedInput leaks event (execution.recall owner)
            (execution.observe app owner),
              runtime.readyActivationCount leaks event (execution.recall owner)⟩] ∧
    (exhaustedClocks (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log).length =
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
  refine ⟨newCounted, ?_, ?_, ?_, ?_⟩
  · rw [newLog]
    intro entry member
    rcases List.mem_append.mp member with prior | last
    · exact unresolved entry prior
    · have same : entry = ⟨query, .activation⟩ := by simpa only [List.mem_singleton] using last
      subst entry
      exact Or.inl rfl
  · rw [newLog]
    intro entry member
    rcases List.mem_append.mp member with prior | last
    · exact emitted entry prior
    · have same : entry = ⟨query, .activation⟩ := by simpa only [List.mem_singleton] using last
      subst entry
      change (runtime.ownerSeedInput leaks event (execution.recall owner)
        (execution.observe app owner)).emitted =
          runtime.ownerEmissionsAtActivation leaks event (execution.recall owner)
            memory.activationIndex
      rw [indexMatch]
      simpa only [List.append_nil] using runtime.ownerSeedInput_emitted_eq_atActivation leaks event
        (execution.recall owner) [] (execution.observe app owner) (by simp)
  · rw [newLog]
    simp only [positiveQueries, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    change positiveQueries memory.log ++ [query] = _
    rw [positiveMatch]
    simp only [query, indexMatch]
  · rw [newLog]
    change (exhaustedClocks (memory.log ++ [⟨query, .activation⟩])).length = _
    simp only [exhaustedClocks, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
    change (exhaustedClocks memory.log).length = _
    rw [clocks, List.length_range,
      runtime.seedInput_eq_of_inputRecall leaks execution recalled owner event]

end Vegas.EventGraphRuntime.LocalSeedController
