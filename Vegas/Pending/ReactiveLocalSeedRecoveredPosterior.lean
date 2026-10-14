/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedPosteriorLog

/-! # Actual seed conditioning after operational raw-log recovery

When an actual observation determines the private raw query log on the
supported scheduler fiber, conditioning on that log is redundant. Its
filtered local factor is then the actual scheduler posterior factor.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Operationally recovered raw logs give the concrete scheduler posterior
its filtered local product factor. The recovery premise concerns only actual
logged queries on supported seeds, not any desired posterior identity. -/
theorem posterior_of_recovered_log (laws : (side : Bool) → PMF (A side))
    (past : List (app).EnvironmentEntry) (log : List (LocalSeedEntry graph (app).Command))
    (positive : ∃ values ∈ {values : (side : Bool) → A side |
        controller.followsFrom remainder (initialMemory (values false) (values true)) [] past ∧
          (controller.replay remainder
            (initialMemory (values false) (values true)) past).log = log},
      values ∈ (independentProduct laws).support)
    (recovered : ∀ values ∈
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).posterior past).support,
      (controller.replay remainder
        (initialMemory (values false) (values true)) past).log = log) :
    ∃ (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (updated : (side : Bool) → PMF (A side)),
      (((app).schedulerMixture (independentProduct laws) (fun values =>
        controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))).posterior past) =
            independentProduct updated ∧
      updated false = (laws false).filter {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply} localPositive := by
  classical
  let current := (((app).schedulerMixture (independentProduct laws) (fun values =>
    controller.fixedScheduler remainder
      (initialMemory (values false) (values true)))).posterior past)
  let logOf := fun values : (side : Bool) → A side =>
    (controller.replay remainder (initialMemory (values false) (values true)) past).log
  have compatible : ∃ values ∈ {values : (side : Bool) → A side |
      controller.followsFrom remainder (initialMemory (values false) (values true)) [] past},
      values ∈ (independentProduct laws).support := by
    obtain ⟨values, both, supported⟩ := positive
    exact ⟨values, both.1, supported⟩
  have logPresent : ∃ values ∈ {values | logOf values = log}, values ∈ current.support := by
    obtain ⟨values, both, supported⟩ := positive
    refine ⟨values, both.2, ?_⟩
    dsimp only [current]
    rw [controller.posterior_follows remainder _ past compatible]
    exact (PMF.mem_support_filter_iff compatible).mpr ⟨both.1, supported⟩
  have unchanged : fiberPosterior current logOf log = current := by
    rw [fiberPosterior_eq_filter _ _ logPresent]
    exact filter_of_support_subset current _ logPresent recovered
  obtain ⟨localPositive, updated, productEq, localEq⟩ :=
    controller.posterior_transcript_log remainder laws past log positive
  refine ⟨localPositive, updated, ?_, localEq⟩
  change fiberPosterior current logOf log = independentProduct updated at productEq
  rwa [unchanged] at productEq

end Vegas.EventGraphRuntime.LocalSeedController
