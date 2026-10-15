/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedReplay
import Interaction.ReactiveSchedulerTranscript

/-! # The actual scheduler posterior filters concrete command consistency

An immutable initial seed pair selects the concrete locally queried scheduler.
Conditioning its recorded commands is exactly filtering the initial seed law
on deterministic replay consistency, with no likelihood-factorization premise.
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
  (remainder : SeedRemainderController runtime leaks RestSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

theorem followsFrom_append (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (earlier left right : List (app).EnvironmentEntry) :
    controller.followsFrom remainder memory earlier (left ++ right) ↔
      controller.followsFrom remainder memory earlier left ∧
        controller.followsFrom remainder (controller.replayFrom remainder memory earlier left)
          (earlier ++ left) right := by
  induction left generalizing memory earlier with
  | nil => simp only [List.nil_append, followsFrom, replayFrom, List.append_nil, true_and]
  | cons entry rest ih =>
      simp only [List.cons_append, followsFrom, ih, replayFrom, List.append_assoc,
        List.nil_append, and_assoc]

theorem follows_snoc (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry) :
    controller.followsFrom remainder memory [] (past ++ [entry]) ↔
      controller.followsFrom remainder memory [] past ∧
        (controller.step remainder (controller.replay remainder memory past)
          past entry.beforeView).1 = entry.command := by
  simp only [controller.followsFrom_append, followsFrom, List.nil_append, and_true, replay]

variable {A : Bool → Type}
  (localController : LocalSeedController runtime leaks (A false) owner event)
  (restController : SeedRemainderController runtime leaks (A true) owner event)

/-- The actual scheduler's immutable-seed posterior is precisely the initial
law filtered by its concrete replayed command transcript. -/
theorem posterior_follows (prior : PMF ((side : Bool) → A side))
    (past : List (app).EnvironmentEntry)
    (positive : ∃ values ∈ {values : (side : Bool) → A side |
        localController.followsFrom restController
          (initialMemory (values false) (values true)) [] past}, values ∈ prior.support) :
    ((app).schedulerMixture prior (fun values => localController.fixedScheduler restController
      (initialMemory (values false) (values true)))).posterior past =
      prior.filter {values : (side : Bool) → A side |
        localController.followsFrom restController
          (initialMemory (values false) (values true)) [] past} positive := by
  let choose (values : (side : Bool) → A side)
      (before : List (app).EnvironmentEntry) (view : (app).EnvironmentView) : (app).Command :=
    (localController.step restController
      (localController.replay restController
        (initialMemory (values false) (values true)) before) before view).1
  have compatible (values : (side : Bool) → A side) (recorded : List (app).EnvironmentEntry) :
      (app).commandConsistentFrom choose values [] recorded ↔
        localController.followsFrom restController
          (initialMemory (values false) (values true)) [] recorded := by
    induction recorded using List.reverseRecOn with
    | nil => rfl
    | append_singleton earlier entry ih =>
        simp only [ReactiveApplication.commandConsistent_snoc, follows_snoc, ih, choose]
  have matched : {values | (app).commandConsistentFrom choose values [] past} =
      {values | localController.followsFrom restController
        (initialMemory (values false) (values true)) [] past} :=
    Set.ext (fun values => compatible values past)
  have possible : ∃ values ∈ {values | (app).commandConsistentFrom choose values [] past},
      values ∈ prior.support := by
    obtain ⟨values, follows, supported⟩ := positive
    exact ⟨values, (compatible values past).mpr follows, supported⟩
  have result := (app).schedulerMixture_posterior_eq_filter prior choose past possible
  have familyEq : (fun values before view => PMF.pure (choose values before view)) =
      (fun values => localController.fixedScheduler restController
        (initialMemory (values false) (values true))) := by
    rfl
  rw [familyEq] at result
  simpa only [matched] using result

end Vegas.EventGraphRuntime.LocalSeedController
