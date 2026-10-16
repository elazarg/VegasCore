/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearPhasePersistence
import Vegas.Pending.PhaseClearTraceProgress

/-! # A clear unfinished event pins its actual installed interval -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Between actual history prefixes, a clear endpoint with an unfinished
event cannot have left the interval containing that event. All raw packets,
automatic operations and ordinary phase normalization are included. -/
theorem phase_phases_eq_of_clear_unfinished_prefix
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (trace : (menu.protocol initial horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix prior trace)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : before.execution.application.phases = phase :: remaining)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (clear : after.execution.application.current.excluded = ∅)
    (unfinished : event ∉ after.execution.application.current.native.config.cut.completed) :
    after.execution.application.phases = before.execution.application.phases := by
  let app := phaseApplication runtime leaks
  have along : ∀ {state} {history : (menu.protocol initial horizon scheduler).Trace state},
      TracePrefix prior history → ∃ next : app.Control, state = some next ∧
        (next.execution.application.current.excluded = ∅ →
          event ∉ next.execution.application.current.native.config.cut.completed →
          next.execution.application.phases = before.execution.application.phases) := by
    intro state history retained
    induction retained with
    | refl => exact ⟨before, rfl, fun _ _ => rfl⟩
    | @extend source target earlier retained joint legal reached ih =>
        obtain ⟨middle, rfl, previous⟩ := ih
        have realized : target ∈ (app.transition initial horizon scheduler (some middle)
            joint).support := reached
        obtain ⟨next, rfl, _⟩ := app.transition_recall_prefix initial horizon scheduler
          middle target joint realized
        refine ⟨next, rfl, fun endpointClear endpointUnfinished => ?_⟩
        have monotone := (phaseApplication_exclusion_monotone runtime leaks).transition
          initial horizon scheduler middle next joint realized
        have middleClear : middle.execution.application.current.excluded = ∅ :=
          Finset.subset_empty.mp (endpointClear ▸ monotone)
        have completed := ((phaseApplication_clear_nativeProgress runtime leaks).transition
          initial horizon scheduler middle next joint realized endpointClear).2.2.2
        have middleUnfinished :
            event ∉ middle.execution.application.current.native.config.cut.completed :=
          fun present => endpointUnfinished (completed present)
        have same := previous middleClear middleUnfinished
        have kept := (phaseApplication_clear_phasePersistence runtime leaks).transition
          initial horizon scheduler middle next joint realized endpointClear phase remaining
            (same.trans installed) event inside endpointUnfinished
        exact kept.trans same
  obtain ⟨next, same, result⟩ := along isPrefix
  cases Option.some.inj same
  exact result clear unfinished

/-- A genuine clear ready endpoint pins every intermediate callback to the
same installed interval, with original native writes retained. This derives
the physical commitment-block guard needed by continuation likelihood bounds. -/
theorem phase_interval_of_between_clear_ready
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (entry final : (phaseApplication runtime leaks).Control)
    (entryTrace : (menu.protocol initial horizon scheduler).Trace (some entry))
    (finalTrace : (menu.protocol initial horizon scheduler).Trace (some final))
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : entry.execution.application.phases = phase :: remaining)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (clear : final.execution.application.current.excluded = ∅)
    (ready : final.execution.application.current.native.config.cut.Ready event)
    (middle : (phaseApplication runtime leaks).Control)
    (middleTrace : (menu.protocol initial horizon scheduler).Trace (some middle))
    (earlier : TracePrefix entryTrace middleTrace) (later : TracePrefix middleTrace finalTrace) :
    middle.execution.application.current.excluded = ∅ ∧
      middle.execution.application.phases = phase :: remaining := by
  have progress := phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon scheduler
    middle final middleTrace finalTrace later clear
  have unfinished : event ∉ middle.execution.application.current.native.config.cut.completed :=
    fun present => ready.1 (progress.2.2.2.2 present)
  exact ⟨progress.1,
    (phase_phases_eq_of_clear_unfinished_prefix runtime leaks menu initial horizon scheduler entry
      middle entryTrace middleTrace earlier phase remaining installed event inside progress.1
        unfinished).trans installed⟩

end Vegas.EventGraphRuntime
