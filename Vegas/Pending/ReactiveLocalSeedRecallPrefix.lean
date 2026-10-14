/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedOwnerRecall
import Vegas.Pending.ReactiveLocalSeedExhaustionRun

/-! # Owner recall prefixes at local activation indices

During a surviving ready interval every further owner response is recorded
as ready. Its local activation count therefore reconstructs the exact earlier
recall prefix from the final full owner recall.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- The maximal earlier recall prefix at a local ready-activation count. -/
def ownerRecallAtActivation (event : graph.EventId) (past : List (app).PlayerEntry)
    (activationIndex : Nat) : List (app).PlayerEntry :=
  past.take (past.length - (runtime.readyActivationCount leaks event past - activationIndex))

/-- The selected-event emitted prefix reconstructed at a local activation index. -/
def ownerEmissionsAtActivation (event : graph.EventId) (past : List (app).PlayerEntry)
    (activationIndex : Nat) : List (Message Player (WitnessedPacket graph)) :=
  ((app).outputs (runtime.ownerRecallAtActivation leaks event past activationIndex)).filter
    fun message => message.payload.call.event? graph = some event

/-- If all later owner entries are ready responses, its old activation count
recovers the complete original recall, including earlier unrelated responses. -/
theorem ownerRecallAtActivation_eq_prefix (event : graph.EventId)
    (past suffix : List (app).PlayerEntry)
    (ready : ∀ entry ∈ suffix, entry.beforeView.application.publicView.EventReady event) :
    runtime.ownerRecallAtActivation leaks event (past ++ suffix)
      (runtime.readyActivationCount leaks event past) = past := by
  classical
  have filtered : (suffix.filter fun entry =>
      entry.beforeView.application.publicView.EventReady event) = suffix := by
    apply List.filter_eq_self.mpr
    intro entry member
    simpa only [decide_eq_true_eq] using ready entry member
  have countEq : runtime.readyActivationCount leaks event (past ++ suffix) =
      runtime.readyActivationCount leaks event past + suffix.length := by
    simp only [readyActivationCount, List.filter_append, List.length_append]
    rw [filtered]
  rw [ownerRecallAtActivation, countEq, List.length_append]
  simp

/-- Authored selected-event input at a ready prefix is a readout of full
later own recall and its current local activation index. -/
theorem ownerSeedInput_emitted_eq_atActivation (event : graph.EventId)
    (past suffix : List (app).PlayerEntry) (view : (app).PlayerView)
    (ready : ∀ entry ∈ suffix, entry.beforeView.application.publicView.EventReady event) :
    (runtime.ownerSeedInput leaks event past view).emitted =
      runtime.ownerEmissionsAtActivation leaks event (past ++ suffix)
        (runtime.readyActivationCount leaks event past) := by
  rw [ownerEmissionsAtActivation,
    runtime.ownerRecallAtActivation_eq_prefix leaks event past suffix ready]
  rfl

private theorem respond_recall_entry (execution : (app).Execution) (owner : Player)
    (action : (app).Action) :
    ∃ emitted, (execution.respond app owner action).recall owner =
      execution.recall owner ++ [⟨execution.observe app owner, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨none, by simp only [ReactiveApplication.Execution.respond, ↓reduceIte]⟩
  | some material =>
      exact ⟨some (execution.network.submit owner
        ((app).packet ((app).submit execution.application owner material) owner
          (execution.network.known owner) material)).1, by
            simp only [ReactiveApplication.Execution.respond, ↓reduceIte]⟩

/-- An actual dispatch from readiness appends only ready entries to this
owner's recall, even when other commands complete the event without a response. -/
theorem dispatch_ready_recall_suffix (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command) (owner : Player)
    (event : graph.EventId) (ready : execution.application.publicView.EventReady event)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    ∃ suffix, next.recall owner = execution.recall owner ++ suffix ∧
      ∀ entry ∈ suffix, entry.beforeView.application.publicView.EventReady event := by
  classical
  obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recallEq := (app).environmentStep_recall execution middle command moved
  cases command with
  | activate actor =>
      change next ∈ ((players actor (middle.recall actor) (middle.observe app actor)).map
        (middle.respond app actor)).support at responded
      obtain ⟨action, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp responded
      by_cases same : actor = owner
      · subst actor
        have applicationEq : middle.application = execution.application := by
          simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at moved
          obtain ⟨selected, possible, pointEq⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
          rw [← pointEq]
          rfl
        obtain ⟨emitted, recorded⟩ := runtime.respond_recall_entry leaks middle owner action
        refine ⟨[⟨middle.observe app owner, action, emitted⟩], ?_, ?_⟩
        · rw [recorded, recallEq]
        · intro entry member
          have sameEntry := List.mem_singleton.mp member
          subst entry
          change middle.application.publicView.EventReady event
          rwa [applicationEq]
      · refine ⟨[], ?_, by simp⟩
        rw [(app).respond_recall_other middle actor owner (Ne.symm same) action, recallEq,
          List.append_nil]
  | application operation =>
      cases (PMF.mem_support_pure_iff _ _).mp responded
      exact ⟨[], by rw [recallEq, List.append_nil], by simp⟩
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp responded
      exact ⟨[], by rw [recallEq, List.append_nil], by simp⟩
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp responded
      exact ⟨[], by rw [recallEq, List.append_nil], by simp⟩

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

/-- Every actual future owner response in a surviving ready interval was
made while the selected event remained ready. No scheduler domain is assumed. -/
theorem runJoint_ready_recall_suffix
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (count : Nat) (execution next : (app).Execution)
    (memory after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (valid : execution.application.Invariant inputs)
    (ready : execution.application.publicView.EventReady event)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) :
    ∃ suffix, next.recall owner = execution.recall owner ++ suffix ∧
      ∀ entry ∈ suffix, entry.beforeView.application.publicView.EventReady event := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨[], (List.append_nil _).symm, by simp⟩
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have first := runtime.reactive_dispatch_progress leaks inputs players execution middle _
        valid moved
      obtain ⟨ticks, progress⟩ := controller.runJoint_progress localLaw remainderLaw remainder
        inputs
        players count middle _ next after first.invariant later
      have middleUnfinished : event ∉ middle.application.config.cut.completed :=
        fun completed => unfinished (progress.completed completed)
      have middleReady : middle.application.publicView.EventReady event := by
        apply (middle.application.publicView_eventReady event).mpr
        rcases first.ready_or_completed event
          ((execution.application.publicView_eventReady event).mp ready) with done | ready
        · exact False.elim (middleUnfinished done)
        · exact ready
      obtain ⟨firstSuffix, firstRecall, firstEntries⟩ := runtime.dispatch_ready_recall_suffix leaks
        players execution middle _ owner event ready moved
      obtain ⟨lastSuffix, lastRecall, lastEntries⟩ := ih middle _ first.invariant middleReady later
      refine ⟨firstSuffix ++ lastSuffix, ?_, ?_⟩
      · rw [lastRecall, firstRecall, List.append_assoc]
      · intro entry member
        rcases List.mem_append.mp member with before | after
        · exact firstEntries entry before
        · exact lastEntries entry after

end Vegas.EventGraphRuntime.LocalSeedController
