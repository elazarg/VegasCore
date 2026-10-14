/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedActivation

/-! # Closed local clocks before actual time advancement

The concrete controller drains repeated current-clock activations before
advancing time. An exhaustion is memoized and cannot precede a further local
owner activation at that same clock.
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

/-- A real ready-owner activation cannot follow an exhaustion at the same clock. -/
theorem activation_not_closed
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (execution : (app).Execution)
    (ready : execution.application.publicView.EventReady event)
    (activated : (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).1 = .activate owner) :
    memory.closedAt ≠ some
      (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed := by
  classical
  intro closed
  have different := (remainder.safe memory.remainderSeed execution.environmentRecall
    (execution.observeEnvironment app)).1 ready
  have commandEq : (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).1 =
        (remainder.choose memory.remainderSeed execution.environmentRecall
          (execution.observeEnvironment app)).2 := by
    simp only [step, closed, ↓reduceIte, ite_self]
  exact different (commandEq.symm.trans activated)

/-- An actual clock-advance command has already recorded the selected event's
current exhaustion; a resolving service command cannot advance the clock. -/
theorem advance_closed
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (execution : (app).Execution)
    (genuine : controller.domain execution)
    (ready : execution.application.publicView.EventReady event)
    (advanced : (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).1 = .application .advanceClock) :
    (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.closedAt = some
        (runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed := by
  classical
  have readyAtView : PublicView.EventReady
      (execution.observeEnvironment app).application event := ready
  dsimp only [step] at advanced ⊢
  rw [ite_eq_left readyAtView] at advanced ⊢
  split_ifs at advanced ⊢ with closed polled
  · exact closed
  · let query : CurrentSeedQuery graph :=
      ⟨runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app),
        memory.activationIndex⟩
    change (finishReply owner memory _ query
      (controller.reply memory.localSeed query)).1 = .application .advanceClock at advanced
    cases answerEq : controller.reply memory.localSeed query with
    | activation =>
        simp only [answerEq, finishReply] at advanced
        cases advanced
    | resolution command =>
        simp only [answerEq, finishReply] at advanced
        have resolves := controller.resolves memory.localSeed query execution command genuine
          rfl ready (controller.service_of_resolution memory.localSeed query command answerEq)
        simpa only [advanced] using resolves.1
    | exhausted =>
        change (finishReply owner memory _ query .exhausted).2.closedAt = _
        rfl
  · exfalso
    apply polled
    change (remainder.choose memory.remainderSeed execution.environmentRecall
      (execution.observeEnvironment app)).2 = .application .advanceClock at advanced
    rw [advanced]
    cases (remainder.choose memory.remainderSeed execution.environmentRecall
      (execution.observeEnvironment app)).1 <;> rfl

end Vegas.EventGraphRuntime.LocalSeedController
