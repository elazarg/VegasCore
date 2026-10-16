/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingWaitingLaw
import Vegas.Pending.PhaseBindingRecallOrder
import Vegas.Pending.PhaseClearRequestAddress

/-! # Earlier physical binding sends cannot read a still-unsent source coordinate -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- Every successful source decoder query names its original static event,
including a query made at an explicitly recorded physical input. -/
theorem phaseSourceView?_input_position (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (input : (phaseApplication runtime leaks).PlayerView)
    (view : SourceProgram.ProtocolView who setup.program)
    (decoded : phaseSourceView? setup mode runtime leaks who event input = some view) :
    ProtocolView.position who setup.program view = event.val := by
  unfold phaseSourceView? at decoded
  split at decoded
  · exact decodeEventView?_position setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputRef setup.program) who event _ _ view decoded
  · cases decoded

variable [Fintype Player] (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- At a genuine clear unsent binding callback, every earlier binding-send
occurrence queried a different source information coordinate. Static decoder
positions and actual clear request addresses derive this even across phases;
no sorted-word, source-origin, or same-attempt premise is supplied. -/
theorem phaseSourceView?_ne_recorded_binding_of_unsent {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (earlier : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (later : List (app).PlayerEntry)
    (recalled : control.execution.recall who = earlier ++ entry :: later)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (transmitted : entry.action.transmission = some material)
    (event : (serviceGraph setup mode).EventId) (candidate : Handle (serviceGraph setup mode))
    (named : material.call.packet = .commitment event candidate)
    (selected : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout selected = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, selected⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩) :
    phaseSourceView? setup mode runtime leaks who event entry.beforeView ≠
      phaseSourceView? setup mode runtime leaks who selected
        (control.execution.observe (app) who) := by
  intro same
  obtain ⟨view, decoded⟩ := phaseSourceView?_succeeds setup mode runtime leaks control.execution
    who selected request.2.2.1 request.2.2.2.1
    (by simp only [binding, EventField.IsPublication, not_false_eq_true])
  have previousDecoded := same.trans decoded
  have previousPosition := phaseSourceView?_input_position setup mode runtime leaks who event
    entry.beforeView view previousDecoded
  have currentPosition := phaseSourceView?_position setup mode runtime leaks control.execution
    who selected view decoded
  have eventEq : event = selected := Fin.ext (previousPosition.symm.trans currentPosition)
  obtain ⟨before, prior, isPrefix, _active, _past, viewed, previousRequest, _allowed⟩ :=
    PhaseCount.recorded_binding_request runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler trace clear who
      earlier entry later recalled material transmitted event candidate named
  have previousClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before control prior trace isPrefix clear).1
  have oldRaw := (menu).toRawTrace initial horizon scheduler prior
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have oldAddress := phase_request_address_of_clear runtime leaks plan inputs horizon scheduler
    oldRaw previousClear who ⟨before.execution.application.attempt, event⟩ previousRequest
  have currentAddress := phase_request_address_of_clear runtime leaks plan inputs horizon scheduler
    raw clear who ⟨control.execution.application.attempt, selected⟩ request
  have attemptEq : entry.beforeView.application.2.attempt =
      control.execution.application.attempt := by
    rw [viewed]
    change before.execution.application.attempt = control.execution.application.attempt
    exact oldAddress.trans (eventEq ▸ currentAddress.symm)
  have earlierRank := PhaseCount.recorded_binding_rank_lt_of_unsent_request runtime leaks bounds
    plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler trace clear who
    earlier entry later recalled material transmitted event candidate named attemptEq selected
    request unsent
  rw [eventEq] at earlierRank
  exact (Nat.lt_irrefl _) earlierRank

end Vegas
