/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearNativeProgress
import GameTheoryExtensions.Protocol.TracePrefix
import Interaction.ReactiveResponseMenu

/-! # Actual clear history prefixes retain native semantic provenance -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- At a clear actual information fiber, every initialized prefix is clear and
its native binding associations and effective semantic history are retained.
This applies to arbitrary raw menus and scheduler choices across phase advances. -/
theorem phase_clear_nativeProgress_of_prefix
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (beforeTrace : (menu.protocol initial horizon scheduler).Trace (some before))
    (afterTrace : (menu.protocol initial horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅) :
    before.execution.application.current.excluded = ∅ ∧
      KeepsStore before.execution.application.current.native
        after.execution.application.current.native ∧
      before.execution.application.current.native.config.history.IsPrefix
        after.execution.application.current.native.config.history ∧
      (∀ field candidate, before.execution.application.current.native.accepted field =
        some candidate → after.execution.application.current.native.accepted field =
          some candidate) ∧
      before.execution.application.current.native.config.cut.completed ⊆
        after.execution.application.current.native.config.cut.completed := by
  let app := phaseApplication runtime leaks
  have along : ∀ {target} {targetTrace : (menu.protocol initial horizon scheduler).Trace target},
      TracePrefix beforeTrace targetTrace → ∃ next : app.Control, target = some next ∧
        (next.execution.application.current.excluded = ∅ →
          before.execution.application.current.excluded = ∅ ∧
          KeepsStore before.execution.application.current.native
            next.execution.application.current.native ∧
          before.execution.application.current.native.config.history.IsPrefix
            next.execution.application.current.native.config.history ∧
          (∀ field candidate, before.execution.application.current.native.accepted field =
            some candidate → next.execution.application.current.native.accepted field =
              some candidate) ∧
          before.execution.application.current.native.config.cut.completed ⊆
            next.execution.application.current.native.config.cut.completed) := by
    intro target targetTrace retained
    induction retained with
    | refl =>
        exact ⟨before, rfl, fun valid =>
          ⟨valid, fun _ _ present => present, ⟨[], by simp⟩, fun _ _ present => present,
            fun _ member => member⟩⟩
    | @extend source target prior retained joint legal reached ih =>
        obtain ⟨middle, rfl, previous⟩ := ih
        have realized : target ∈ (app.transition initial horizon scheduler (some middle)
            joint).support := reached
        obtain ⟨next, rfl, _⟩ := app.transition_recall_prefix initial horizon scheduler
          middle target joint realized
        refine ⟨next, rfl, fun valid => ?_⟩
        have monotone := (phaseApplication_exclusion_monotone runtime leaks).transition
          initial horizon scheduler middle next joint realized
        have middleClear : middle.execution.application.current.excluded = ∅ :=
          Finset.subset_empty.mp (valid ▸ monotone)
        obtain ⟨firstClear, firstStore, firstHistory, firstAccepted, firstCompleted⟩ :=
          previous middleClear
        obtain ⟨lastStore, lastHistory, lastAccepted, lastCompleted⟩ :=
          (phaseApplication_clear_nativeProgress runtime leaks).transition initial horizon
            scheduler middle next joint realized valid
        exact ⟨firstClear, fun field value present => lastStore field value
          (firstStore field value present), firstHistory.trans lastHistory,
          fun field candidate present => lastAccepted field candidate
            (firstAccepted field candidate present), firstCompleted.trans lastCompleted⟩
  obtain ⟨next, same, result⟩ := along isPrefix
  cases Option.some.inj same
  exact result clear

/-- Readiness at an earlier physical prefix can disappear only by completion
while the endpoint remains clear; a phase advance cannot erase it. -/
theorem phase_ready_or_completed_of_clear_prefix
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (beforeTrace : (menu.protocol initial horizon scheduler).Trace (some before))
    (afterTrace : (menu.protocol initial horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅)
    (event : graph.EventId)
    (ready : before.execution.application.current.native.config.cut.Ready event) :
    event ∈ after.execution.application.current.native.config.cut.completed ∨
      after.execution.application.current.native.config.cut.Ready event := by
  have completed := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before after beforeTrace afterTrace isPrefix clear).2.2.2.2
  by_cases done : event ∈ after.execution.application.current.native.config.cut.completed
  · exact Or.inl done
  · exact Or.inr ⟨done, ready.2.trans completed⟩

end Vegas.EventGraphRuntime
