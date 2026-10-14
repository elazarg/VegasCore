/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedScheduler

/-! # Local seed queries at actual owner decisions

An actual selected owner activation at a ready event is a genuine positive
local query. Its input is reconstructed from that owner's real recall/view,
and its activation index advances once even when the public clock stutters.
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

/-- At a genuine ready-owner decision the new private log entry is exactly
its actual observable local input and a positive activation reply. -/
theorem activation_log
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (execution : (app).Execution)
    (genuine : controller.domain execution)
    (recalled : execution.InputRecall app)
    (ready : execution.application.publicView.EventReady event)
    (activated : (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).1 = .activate owner) :
    (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2 =
      { memory with
        activationIndex := memory.activationIndex + 1
        log := memory.log ++ [⟨⟨runtime.ownerSeedInput leaks event (execution.recall owner)
          (execution.observe app owner), memory.activationIndex⟩, .activation⟩] } := by
  classical
  have notFallback := (remainder.safe memory.remainderSeed execution.environmentRecall
    (execution.observeEnvironment app)).1 ready
  dsimp only [step] at activated ⊢
  split_ifs at activated ⊢ with isReady closed polled
  · exact False.elim (notFallback activated)
  · let query : CurrentSeedQuery graph :=
      ⟨runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app), memory.activationIndex⟩
    change (finishReply owner memory _ query
      (controller.reply memory.localSeed query)).1 = .activate owner at activated
    cases answerEq : controller.reply memory.localSeed query with
    | activation =>
        change (finishReply owner memory _ query .activation).2 = _
        simp only [finishReply, query]
        rw [runtime.seedInput_eq_of_inputRecall leaks execution recalled owner event]
    | resolution command =>
        simp only [answerEq, finishReply] at activated
        have resolves := controller.resolves memory.localSeed query execution command genuine
          rfl ready (controller.service_of_resolution memory.localSeed query command answerEq)
        have impossible : command ≠ .activate owner := by
          intro same
          simpa only [same] using resolves.1
        exact False.elim (impossible activated)
    | exhausted =>
        simp only [answerEq, finishReply] at activated
        exact False.elim (notFallback activated)
  · exact False.elim (notFallback activated)
  · exact False.elim (notFallback activated)

end Vegas.EventGraphRuntime.LocalSeedController
