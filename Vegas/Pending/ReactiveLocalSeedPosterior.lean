/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedReplay
import GameTheory.Math.Probability.Conditioning

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

private theorem filter_eq_of_support_eq {Seed : Type} (prior : PMF Seed)
    (first second : Set Seed)
    (firstPositive : ∃ seed ∈ first, seed ∈ prior.support)
    (secondPositive : ∃ seed ∈ second, seed ∈ prior.support)
    (matching : ∀ seed ∈ prior.support, seed ∈ first ↔ seed ∈ second) :
    prior.filter first firstPositive = prior.filter second secondPositive := by
  classical
  have indicatorEq : first.indicator prior = second.indicator prior := by
    funext seed
    by_cases supported : seed ∈ prior.support
    · by_cases member : seed ∈ first
      · simp only [Set.indicator_of_mem member,
          Set.indicator_of_mem ((matching seed supported).mp member)]
      · simp only [Set.indicator_of_notMem member,
          Set.indicator_of_notMem (fun h => member ((matching seed supported).mpr h))]
    · have zero : prior seed = 0 := by
        change ¬ prior seed ≠ 0 at supported
        exact Classical.not_not.mp supported
      simp only [Set.indicator, zero, ite_self]
  ext seed
  simp only [PMF.filter_apply, indicatorEq]

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
  classical
  induction past using List.reverseRecOn with
  | nil =>
      change prior = _
      exact (filter_of_support_subset prior _ positive (by intro values _; trivial)).symm
  | append_singleton past entry ih =>
      let earlier : Set ((side : Bool) → A side) := {values |
        localController.followsFrom restController
          (initialMemory (values false) (values true)) [] past}
      let full : Set ((side : Bool) → A side) := {values |
        localController.followsFrom restController
          (initialMemory (values false) (values true)) [] (past ++ [entry])}
      have included : full ⊆ earlier := fun values compatible =>
        ((localController.follows_snoc restController _ _ _).mp compatible).1
      have earlierPositive : ∃ values ∈ earlier, values ∈ prior.support := by
        obtain ⟨values, compatible, supported⟩ := positive
        exact ⟨values, included compatible, supported⟩
      let current := prior.filter earlier earlierPositive
      let choose (values : (side : Bool) → A side) : (app).Command :=
        (localController.step restController
          (localController.replay restController
            (initialMemory (values false) (values true)) past) past entry.beforeView).1
      have fullPositive : ∃ values ∈ full, values ∈ current.support := by
        obtain ⟨values, compatible, supported⟩ := positive
        exact ⟨values, compatible, (PMF.mem_support_filter_iff earlierPositive).mpr
          ⟨included compatible, supported⟩⟩
      have nextPositive : ∃ values ∈ {values | choose values = entry.command},
          values ∈ current.support := by
        obtain ⟨values, compatible, supported⟩ := fullPositive
        exact ⟨values, ((localController.follows_snoc restController _ _ _).mp compatible).2,
          supported⟩
      have postEq := ih earlierPositive
      rw [ReactiveApplication.SchedulerImplementation.posterior_snoc, postEq]
      simp only [ReactiveApplication.schedulerMixture, fixedScheduler, PMF.pure_map]
      change (fiberPosterior (current.map fun values => (choose values, values))
        Prod.fst entry.command).map Prod.snd = prior.filter full positive
      have tagged := fiberPosterior_bind_of_observation current
        (fun values => PMF.pure (choose values, values)) choose Prod.fst
        (fun _ _ result supported => by
          cases (PMF.mem_support_pure_iff _ _).mp supported
          rfl) entry.command (mem_support_map_of_exists_mem_fiber nextPositive)
      change fiberPosterior (current.map fun values => (choose values, values))
        Prod.fst entry.command = _ at tagged
      rw [tagged, PMF.map_bind]
      simp only [PMF.pure_map, PMF.bind_pure]
      rw [fiberPosterior_eq_filter _ _ nextPositive]
      have conditioned := filter_eq_of_support_eq current
        {values | choose values = entry.command} full nextPositive fullPositive
        (fun values supported => by
          have old := ((PMF.mem_support_filter_iff earlierPositive).mp supported).1
          exact ⟨fun next => (localController.follows_snoc restController _ _ _).mpr
            ⟨old, next⟩, fun whole =>
              ((localController.follows_snoc restController _ _ _).mp whole).2⟩)
      rw [conditioned]
      exact filter_filter_of_subset prior earlier full earlierPositive fullPositive included

end Vegas.EventGraphRuntime.LocalSeedController
