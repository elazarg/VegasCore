/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedRecallPrefix
import Vegas.Pending.ReactiveLocalSeedEmissionLog

/-! # Actual emission-prefix transitions of the local query log

Every raw query records the selected-event outputs of the owner's actual
recall prefix at its activation index. Later ready responses preserve this
readout for every previously recorded query.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

theorem readyActivationCount_append_ready (event : graph.EventId)
    (past suffix : List (app).PlayerEntry)
    (ready : ∀ entry ∈ suffix, entry.beforeView.application.publicView.EventReady event) :
    runtime.readyActivationCount leaks event (past ++ suffix) =
      runtime.readyActivationCount leaks event past + suffix.length := by
  classical
  have filtered : (suffix.filter fun entry =>
      entry.beforeView.application.publicView.EventReady event) = suffix := by
    apply List.filter_eq_self.mpr
    intro entry member
    simpa only [decide_eq_true_eq] using ready entry member
  simp only [readyActivationCount, List.filter_append, List.length_append]
  rw [filtered]

/-- Later ready responses preserve every already determined earlier recall prefix. -/
theorem ownerRecallAtActivation_append_ready (event : graph.EventId)
    (past suffix : List (app).PlayerEntry) (activationIndex : Nat)
    (bounded : activationIndex ≤ runtime.readyActivationCount leaks event past)
    (ready : ∀ entry ∈ suffix, entry.beforeView.application.publicView.EventReady event) :
    runtime.ownerRecallAtActivation leaks event (past ++ suffix) activationIndex =
      runtime.ownerRecallAtActivation leaks event past activationIndex := by
  rw [ownerRecallAtActivation, ownerRecallAtActivation,
    runtime.readyActivationCount_append_ready leaks event past suffix ready, List.length_append]
  have lengthEq : past.length + suffix.length -
      (runtime.readyActivationCount leaks event past + suffix.length - activationIndex) =
        past.length - (runtime.readyActivationCount leaks event past - activationIndex) := by omega
  rw [lengthEq]
  exact List.take_append_of_le_length (Nat.sub_le _ _)

/-- The owner-visible output prefix at a past activation index remains unchanged. -/
theorem ownerEmissionsAtActivation_append_ready (event : graph.EventId)
    (past suffix : List (app).PlayerEntry) (activationIndex : Nat)
    (bounded : activationIndex ≤ runtime.readyActivationCount leaks event past)
    (ready : ∀ entry ∈ suffix, entry.beforeView.application.publicView.EventReady event) :
    runtime.ownerEmissionsAtActivation leaks event (past ++ suffix) activationIndex =
      runtime.ownerEmissionsAtActivation leaks event past activationIndex := by
  rw [ownerEmissionsAtActivation, ownerEmissionsAtActivation,
    runtime.ownerRecallAtActivation_append_ready leaks event past suffix activationIndex
      bounded ready]

end Vegas.EventGraphRuntime

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- A concrete step retains its log or appends precisely its one actual current query. -/
theorem step_log_eq_or_append
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    (controller.step remainder memory past view).2.log = memory.log ∨
      ∃ reply : LocalSeedReply (app).Command,
        (controller.step remainder memory past view).2.log = memory.log ++
          [⟨⟨runtime.environmentSeedInput leaks owner event view,
            memory.activationIndex⟩, reply⟩] := by
  classical
  dsimp only [step]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨_, finishReply_log ..⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- A real ready dispatch preserves reconstruction of every logged emitted
prefix from the owner's later actual recall and the query's local index. -/
theorem dispatch_log_emittedAtActivation
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    (recalled : execution.InputRecall app)
    (ready : execution.application.publicView.EventReady event)
    (indexed : memory.activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (remembered : ∀ entry ∈ memory.log,
      entry.query.activationIndex ≤
        runtime.readyActivationCount leaks event (execution.recall owner) ∧
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (execution.recall owner) entry.query.activationIndex)
    (reached : next ∈ ((app).dispatch players
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).1 execution).support) :
    ∀ entry ∈ (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log,
      entry.query.activationIndex ≤ runtime.readyActivationCount leaks event (next.recall owner) ∧
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (next.recall owner) entry.query.activationIndex := by
  obtain ⟨suffix, recallEq, entriesReady⟩ := runtime.dispatch_ready_recall_suffix leaks players
    execution next _ owner event ready reached
  have countEq : runtime.readyActivationCount leaks event (next.recall owner) =
      runtime.readyActivationCount leaks event (execution.recall owner) + suffix.length := by
    rw [recallEq, runtime.readyActivationCount_append_ready leaks event _ _ entriesReady]
  have retained (entry) (member : entry ∈ memory.log) :
      entry.query.activationIndex ≤ runtime.readyActivationCount leaks event (next.recall owner) ∧
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (next.recall owner) entry.query.activationIndex := by
    obtain ⟨bound, rememberedEq⟩ := remembered entry member
    refine ⟨by rw [countEq]; omega, ?_⟩
    rw [recallEq, runtime.ownerEmissionsAtActivation_append_ready leaks event _ _ _ bound
      entriesReady]
    exact rememberedEq
  rcases controller.step_log_eq_or_append remainder memory execution.environmentRecall
    (execution.observeEnvironment app) with unchanged | ⟨reply, appended⟩
  · rw [unchanged]
    exact retained
  · rw [appended]
    intro entry member
    rcases List.mem_append.mp member with prior | last
    · exact retained entry prior
    · have same := List.mem_singleton.mp last
      subst entry
      refine ⟨?_, ?_⟩
      · change memory.activationIndex ≤ runtime.readyActivationCount leaks event (next.recall owner)
        rw [indexed, countEq]
        omega
      · change (runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).emitted =
            runtime.ownerEmissionsAtActivation leaks event (next.recall owner)
              memory.activationIndex
        rw [runtime.seedInput_eq_of_inputRecall leaks execution recalled owner event,
          indexed, recallEq]
        exact runtime.ownerSeedInput_emitted_eq_atActivation leaks event (execution.recall owner)
          suffix (execution.observe app owner) entriesReady

end Vegas.EventGraphRuntime.LocalSeedController
