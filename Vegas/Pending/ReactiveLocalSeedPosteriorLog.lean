/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedPosterior
import Vegas.Pending.ReactiveLocalSeedConditioning

/-! # Actual scheduler seed posterior at a recovered query log

The actual immutable-seed scheduler posterior, further conditioned on its
private query log, is a product whose local factor filters exactly the logged
local answers. Recovering that log from an owner's information remains an
operational theorem, not a posterior assumption here.
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

/-- The genuine scheduler posterior at a positive transcript/log fiber is
its initial product law filtered by the actual local answers and remainder compatibility. -/
theorem posterior_transcript_log (laws : (side : Bool) → PMF (A side))
    (past : List (app).EnvironmentEntry) (log : List (LocalSeedEntry graph (app).Command))
    (positive : ∃ values ∈ {values : (side : Bool) → A side |
        controller.followsFrom remainder (initialMemory (values false) (values true)) [] past ∧
          (controller.replay remainder
            (initialMemory (values false) (values true)) past).log = log},
      values ∈ (independentProduct laws).support) :
    ∃ (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (updated : (side : Bool) → PMF (A side)),
      fiberPosterior
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).posterior past)
        (fun values => (controller.replay remainder
          (initialMemory (values false) (values true)) past).log) log =
            independentProduct updated ∧
      updated false = (laws false).filter {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply} localPositive := by
  classical
  let prior := independentProduct laws
  let consistent : Set ((side : Bool) → A side) := {values |
    controller.followsFrom remainder (initialMemory (values false) (values true)) [] past}
  let logFiber : Set ((side : Bool) → A side) := {values |
    (controller.replay remainder (initialMemory (values false) (values true)) past).log = log}
  have consistentPositive : ∃ values ∈ consistent, values ∈ prior.support := by
    obtain ⟨values, ⟨compatible, _⟩, supported⟩ := positive
    exact ⟨values, compatible, supported⟩
  let current := prior.filter consistent consistentPositive
  have logPositive : ∃ values ∈ logFiber, values ∈ current.support := by
    obtain ⟨values, ⟨compatible, recorded⟩, supported⟩ := positive
    exact ⟨values, recorded,
      (PMF.mem_support_filter_iff consistentPositive).mpr ⟨compatible, supported⟩⟩
  have conditionEq : current.filter logFiber logPositive =
      prior.filter (consistent ∩ logFiber) positive := by
    let : MeasurableSpace ((side : Bool) → A side) := ⊤
    have consistentMeasurable : MeasurableSet consistent := by trivial
    have logMeasurable : MeasurableSet logFiber := by trivial
    have fullMeasurable : MeasurableSet (consistent ∩ logFiber) := by trivial
    apply PMF.toMeasure_injective
    rw [toMeasure_filter current logFiber logMeasurable logPositive,
      toMeasure_filter prior consistent consistentMeasurable consistentPositive,
      toMeasure_filter prior (consistent ∩ logFiber) fullMeasurable positive,
      ProbabilityTheory.cond_cond_eq_cond_inter consistentMeasurable logMeasurable]
  obtain ⟨localPositive, updated, factorized, localEq⟩ :=
    controller.filter_transcript_log remainder laws past log positive
  refine ⟨localPositive, updated, ?_, localEq⟩
  rw [controller.posterior_follows remainder _ past consistentPositive,
    fiberPosterior_eq_filter _ _ logPositive, conditionEq]
  exact factorized

end Vegas.EventGraphRuntime.LocalSeedController
