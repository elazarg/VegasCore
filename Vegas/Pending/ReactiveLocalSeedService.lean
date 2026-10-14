/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedScheduler

/-! # Concrete successful inclusion certificates for local seed service

The service domain must establish actual pending lookup and application
acceptance. Matching local emissions alone do not establish these facts.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- A genuine pending lookup and successful application handler make this
inclusion an actual completion of the selected event. -/
theorem resolvingSeedCommand_include (event : graph.EventId) (execution : (app).Execution)
    (id : MessageId Player) (packet : Message Player (WitnessedPacket graph))
    (result : State graph) (found : execution.network.lookup id = some packet)
    (handled : (app).handle execution.application packet = some result)
    (completed : event ∈ result.config.cut.completed) :
    runtime.ResolvingSeedCommand leaks event execution (.include id) := by
  refine ⟨trivial, ?_⟩
  intro next reached
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff] at reached
  subst next
  simpa only [ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found, handled, Option.getD_some] using completed

end Vegas.EventGraphRuntime
