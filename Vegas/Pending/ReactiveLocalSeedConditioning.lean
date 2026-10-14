/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedReplay
import GameTheory.Math.Probability.ProductConditioning

/-! # Conditioning actual seed-controller transcripts

The concrete controller's command and query log impose a rectangle on the
independently sampled local and remainder seeds. The local posterior is its
prior filtered by the actual local answers. Observation-level log recovery
is a separate operational requirement.
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

/-- Concrete transcript compatibility filters the local seed exactly by its
logged activation/service answers and leaves a product with the remainder. -/
theorem filter_transcript_log (laws : (side : Bool) → PMF (A side))
    (past : List (app).EnvironmentEntry) (log : List (LocalSeedEntry graph (app).Command))
    (positive : ∃ values ∈ {values : (side : Bool) → A side |
        controller.followsFrom remainder (initialMemory (values false) (values true)) [] past ∧
          (controller.replay remainder
            (initialMemory (values false) (values true)) past).log = log},
      values ∈ (independentProduct laws).support) :
    ∃ (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (updated : (side : Bool) → PMF (A side)),
      (independentProduct laws).filter {values : (side : Bool) → A side |
        controller.followsFrom remainder (initialMemory (values false) (values true)) [] past ∧
          (controller.replay remainder
            (initialMemory (values false) (values true)) past).log = log} positive =
          independentProduct updated ∧
      updated false = (laws false).filter {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply} localPositive := by
  classical
  let restriction : (side : Bool) → Set (A side)
    | false => {seed | ∀ entry ∈ log, controller.reply seed entry.query = entry.reply}
    | true => {seed | ∃ witness : A false,
        controller.followsFrom remainder (initialMemory witness seed) [] past ∧
          (controller.replay remainder (initialMemory witness seed) past).log = log}
  have rectangle : {values : (side : Bool) → A side |
      controller.followsFrom remainder (initialMemory (values false) (values true)) [] past ∧
        (controller.replay remainder
          (initialMemory (values false) (values true)) past).log = log} =
        Set.pi Set.univ restriction := by
    ext values
    change (_ ∧ _) ↔ _
    rw [controller.transcript_log_rectangle remainder past log]
    constructor
    · rintro ⟨answers, realizes⟩ side _
      cases side with
      | false => exact answers
      | true => exact realizes
    · intro listed
      exact ⟨listed false (Set.mem_univ _), listed true (Set.mem_univ _)⟩
  have coordinates (side : Bool) : ∃ value ∈ restriction side,
      value ∈ (laws side).support := by
    obtain ⟨values, compatible, supported⟩ := positive
    have listed : values ∈ Set.pi Set.univ restriction := by rwa [← rectangle]
    exact ⟨values side, listed side (Set.mem_univ _),
      (independentProduct_support_iff laws values).mp supported side⟩
  refine ⟨coordinates false, fun side => (laws side).filter (restriction side)
    (coordinates side), ?_, rfl⟩
  simpa only [← rectangle] using filter_independentProduct laws restriction coordinates

end Vegas.EventGraphRuntime.LocalSeedController
