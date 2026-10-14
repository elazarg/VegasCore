/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedRun

/-! # Immutable-seed replay of the actual local scheduler

Actual environment recall reconstructs all deterministic private bookkeeping.
The concrete execution/private-log law equals the ordinary reactive run under
the scheduler selected by the two initially sampled seeds.
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

variable (remainder : SeedRemainderController runtime leaks RestSeed owner event)

/-- Replay the recorded real scheduler inputs, starting at their actual recall prefix. -/
def replayFrom (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier : List (app).EnvironmentEntry) : List (app).EnvironmentEntry →
      LocalSeedMemory runtime leaks LocalSeed RestSeed
  | [] => memory
  | entry :: rest => replayFrom
      (controller.step remainder memory earlier entry.beforeView).2 (earlier ++ [entry]) rest

/-- Deterministic private bookkeeping reconstructed from actual environment recall. -/
def replay (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) : LocalSeedMemory runtime leaks LocalSeed RestSeed :=
  controller.replayFrom remainder memory [] past

theorem replayFrom_append (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier left right : List (app).EnvironmentEntry) :
    controller.replayFrom remainder memory earlier (left ++ right) =
      controller.replayFrom remainder
        (controller.replayFrom remainder memory earlier left) (earlier ++ left) right := by
  induction left generalizing memory earlier with
  | nil => simp only [List.nil_append, replayFrom, List.append_nil]
  | cons entry rest ih =>
      simp only [List.cons_append, replayFrom, ih, List.append_assoc, List.nil_append]

theorem replay_snoc (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry) :
    controller.replay remainder memory (past ++ [entry]) =
      (controller.step remainder (controller.replay remainder memory past)
        past entry.beforeView).2 := by
  simp only [replay, replayFrom_append, List.nil_append, replayFrom]

/-- Replaying actual inputs retains every already recorded local answer. -/
theorem replayFrom_log_prefix (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier past : List (app).EnvironmentEntry) :
    memory.log <+: (controller.replayFrom remainder memory earlier past).log := by
  induction past generalizing memory earlier with
  | nil => exact List.prefix_refl _
  | cons entry rest ih =>
      exact (controller.step_log_prefix remainder memory earlier entry.beforeView).trans
        (ih _ _)

/-- A seed agreeing with the final actual query log reconstructs all the same
private bookkeeping, not merely the final emitted command. -/
theorem replayFrom_replaceLocal (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier past : List (app).EnvironmentEntry) (seed : LocalSeed)
    (agrees : ∀ entry ∈ (controller.replayFrom remainder memory earlier past).log,
      controller.reply seed entry.query = entry.reply) :
    controller.replayFrom remainder (memory.replaceLocal seed) earlier past =
      (controller.replayFrom remainder memory earlier past).replaceLocal seed := by
  induction past generalizing memory earlier with
  | nil => rfl
  | cons entry rest ih =>
      have logPrefix := controller.replayFrom_log_prefix remainder
        (controller.step remainder memory earlier entry.beforeView).2 (earlier ++ [entry]) rest
      have splice := controller.step_replaceLocal_of_log remainder memory seed earlier
        entry.beforeView (fun query member => agrees query (logPrefix.subset member))
      simp only [replayFrom]
      rw [splice]
      exact ih _ _ agrees

/-- Concrete command consistency for a recorded environment transcript. -/
def followsFrom (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier : List (app).EnvironmentEntry) : List (app).EnvironmentEntry → Prop
  | [] => True
  | entry :: rest =>
      (controller.step remainder memory earlier entry.beforeView).1 = entry.command ∧
        followsFrom
          (controller.step remainder memory earlier entry.beforeView).2 (earlier ++ [entry]) rest

/-- A log-compatible seed preserves the entire actual command transcript. -/
theorem followsFrom_replaceLocal (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier past : List (app).EnvironmentEntry)
    (follows : controller.followsFrom remainder memory earlier past) (seed : LocalSeed)
    (agrees : ∀ entry ∈ (controller.replayFrom remainder memory earlier past).log,
      controller.reply seed entry.query = entry.reply) :
    controller.followsFrom remainder (memory.replaceLocal seed) earlier past := by
  induction past generalizing memory earlier with
  | nil => trivial
  | cons entry rest ih =>
      have logPrefix := controller.replayFrom_log_prefix remainder
        (controller.step remainder memory earlier entry.beforeView).2 (earlier ++ [entry]) rest
      have splice := controller.step_replaceLocal_of_log remainder memory seed earlier
        entry.beforeView (fun query member => agrees query (logPrefix.subset member))
      simp only [followsFrom] at follows ⊢
      rw [splice]
      exact ⟨follows.1, ih _ _ follows.2 agrees⟩

private theorem finishReply_seed (who : Player)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (fallback : (app).Command) (query : CurrentSeedQuery graph)
    (answer : LocalSeedReply (app).Command) :
    (finishReply who memory fallback query answer).2.localSeed = memory.localSeed := by
  cases answer <;> rfl

private theorem step_seed (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    (controller.step remainder memory past view).2.localSeed = memory.localSeed := by
  classical
  dsimp only [step]
  split_ifs <;> first | rfl | exact finishReply_seed _ _ _ _ _

private theorem finishReply_answers
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (fallback : (app).Command) (query : CurrentSeedQuery graph)
    (agrees : ∀ entry ∈ memory.log,
      controller.reply memory.localSeed entry.query = entry.reply) :
    ∀ entry ∈ (finishReply owner memory fallback query
      (controller.reply memory.localSeed query)).2.log,
        controller.reply (finishReply owner memory fallback query
          (controller.reply memory.localSeed query)).2.localSeed entry.query = entry.reply := by
  intro entry member
  rw [finishReply_log] at member
  rw [finishReply_seed]
  rcases List.mem_append.mp member with member | member
  · exact agrees entry member
  · have same := List.mem_singleton.mp member
    subst entry
    rfl

private theorem step_answers (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (agrees : ∀ entry ∈ memory.log,
      controller.reply memory.localSeed entry.query = entry.reply) :
    ∀ entry ∈ (controller.step remainder memory past view).2.log,
      controller.reply (controller.step remainder memory past view).2.localSeed
        entry.query = entry.reply := by
  classical
  dsimp only [step]
  split_ifs
  · exact agrees
  · exact controller.finishReply_answers memory _ _ agrees
  · exact agrees
  · exact agrees

private theorem replayFrom_seed (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier past : List (app).EnvironmentEntry) :
    (controller.replayFrom remainder memory earlier past).localSeed = memory.localSeed := by
  induction past generalizing memory earlier with
  | nil => rfl
  | cons entry rest ih =>
      rw [replayFrom, ih, controller.step_seed]

/-- Every recorded answer is the genuine answer of the retained local seed. -/
theorem replayFrom_answers (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier past : List (app).EnvironmentEntry)
    (agrees : ∀ entry ∈ memory.log,
      controller.reply memory.localSeed entry.query = entry.reply) :
    ∀ entry ∈ (controller.replayFrom remainder memory earlier past).log,
      controller.reply memory.localSeed entry.query = entry.reply := by
  induction past generalizing memory earlier with
  | nil => exact agrees
  | cons entry rest ih =>
      intro query member
      have nextAgrees := controller.step_answers remainder memory earlier entry.beforeView agrees
      have answer := ih _ _ nextAgrees query member
      rwa [controller.step_seed] at answer

/-- Sampled seeds initialize an empty private query log. -/
def initialMemory (localSeed : LocalSeed) (remainderSeed : RestSeed) :
    LocalSeedMemory runtime leaks LocalSeed RestSeed :=
  ⟨localSeed, remainderSeed, 0, none, []⟩

/-- At a fixed actual command transcript and query log, compatibility is a
rectangle: local seeds are constrained exactly by their logged replies, and
the remainder seeds by their ability to realize the transcript with that log. -/
theorem transcript_log_rectangle (past : List (app).EnvironmentEntry)
    (log : List (LocalSeedEntry graph (app).Command)) (localSeed : LocalSeed)
    (remainderSeed : RestSeed) :
    (controller.followsFrom remainder (initialMemory localSeed remainderSeed) [] past ∧
      (controller.replay remainder (initialMemory localSeed remainderSeed) past).log = log) ↔
      (∀ entry ∈ log, controller.reply localSeed entry.query = entry.reply) ∧
        ∃ witness : LocalSeed,
          controller.followsFrom remainder (initialMemory witness remainderSeed) [] past ∧
            (controller.replay remainder (initialMemory witness remainderSeed) past).log = log := by
  constructor
  · rintro ⟨follows, recorded⟩
    refine ⟨?_, localSeed, follows, recorded⟩
    rw [← recorded]
    exact controller.replayFrom_answers remainder (initialMemory localSeed remainderSeed)
      [] past (by simp [initialMemory])
  · rintro ⟨agrees, witness, follows, recorded⟩
    have logAgrees : ∀ entry ∈ (controller.replayFrom remainder
        (initialMemory witness remainderSeed) [] past).log,
        controller.reply localSeed entry.query = entry.reply := by
      change ∀ entry ∈ (controller.replay remainder
        (initialMemory witness remainderSeed) past).log,
          controller.reply localSeed entry.query = entry.reply
      rwa [recorded]
    have followed := controller.followsFrom_replaceLocal remainder
      (initialMemory witness remainderSeed) [] past follows localSeed logAgrees
    have replayed := controller.replayFrom_replaceLocal remainder
      (initialMemory witness remainderSeed) [] past localSeed logAgrees
    refine ⟨followed, ?_⟩
    change (controller.replayFrom remainder
      ((initialMemory witness remainderSeed).replaceLocal localSeed) [] past).log = log
    rw [replayed]
    exact recorded

/-- An immutable pair of seeds selects a scheduler reading genuine environment history. -/
def fixedScheduler (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) :
    (app).Scheduler := fun past view =>
  PMF.pure (controller.step remainder (controller.replay remainder memory past) past view).1

/-- The full actual run and private query log are reconstructed by the scheduler
selected once by the immutable initial seeds. -/
theorem runJoint_replay (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (players : Player → (app).Policy) (count : Nat) (execution : (app).Execution)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) :
    (controller.implementation localLaw remainderLaw remainder).runJoint players count execution
        (controller.replay remainder memory execution.environmentRecall) =
      ((app).runRounds (controller.fixedScheduler remainder memory) players count execution).map
        fun next => (next, controller.replay remainder memory next.environmentRecall) := by
  induction count generalizing execution with
  | zero =>
      simp only [ReactiveApplication.SchedulerImplementation.runJoint,
        ReactiveApplication.runRounds, PMF.pure_map]
  | succ count ih =>
      rw [controller.runJoint_succ]
      simp only [ReactiveApplication.runRounds, ReactiveApplication.round, fixedScheduler,
        PMF.pure_bind, PMF.map_bind]
      apply bind_congr_on_support _
      intro next reached
      have memoryEq :
          (controller.step remainder (controller.replay remainder memory
            execution.environmentRecall) execution.environmentRecall
              (execution.observeEnvironment app)).2 =
            controller.replay remainder memory next.environmentRecall := by
        rw [(app).dispatch_environmentRecall players _ execution next reached]
        exact (controller.replay_snoc remainder memory execution.environmentRecall
          ⟨execution.observeEnvironment app, _⟩).symm
      rw [memoryEq, ih]

/-- At initialization the reconstructed memory is exactly the sampled private memory. -/
theorem runJoint_initial (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (players : Player → (app).Policy) (count : Nat) (state : State graph)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) :
    (controller.implementation localLaw remainderLaw remainder).runJoint players count
        (ReactiveApplication.Execution.initial app state) memory =
      ((app).runRounds (controller.fixedScheduler remainder memory) players count
        (ReactiveApplication.Execution.initial app state)).map
          fun next => (next, controller.replay remainder memory next.environmentRecall) :=
  controller.runJoint_replay remainder localLaw remainderLaw players count
    (ReactiveApplication.Execution.initial app state) memory

end Vegas.EventGraphRuntime.LocalSeedController
