/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseOwnBindingOrder
import Interaction.ReactiveRecordedResponse

/-! # Actual chronological binding records have strict source rank order -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (ordered : graph.RevealRelaxedOrdered)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

include ordered in
/-- A specified nonsilent occurrence in an actual clear recall reconstructs
its genuine ready callback for the event named by that exact raw material. -/
theorem recorded_binding_request {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (earlier : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (later : List (app).PlayerEntry)
    (recalled : control.execution.recall who = earlier ++ entry :: later)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (event : graph.EventId) (candidate : Handle graph)
    (named : material.call.packet = .commitment event candidate) :
    ∃ (before : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some before)),
      TracePrefix prior trace ∧ before.actor = some who ∧
      before.execution.recall who = earlier ∧
      entry.beforeView = before.execution.observe (app) who ∧
      before.execution.application.SeedRequest who ⟨before.execution.application.attempt, event⟩ ∧
      entry.action ∈ onePacketActions runtime leaks bounds who (before.execution.recall who)
        (before.execution.observe (app) who) := by
  obtain ⟨before, prior, isPrefix, active, past, viewed, offered⟩ :=
    (menu).recorded_response_at initial horizon scheduler control trace who earlier entry later
      recalled
  rw [← past] at offered
  have priorClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before control prior trace isPrefix clear).1
  have actionEq : entry.action = ⟨some material⟩ := by
    cases actionAt : entry.action with
    | mk transmission =>
        have actual : transmission = some material := by simpa only [actionAt] using transmitted
        cases actual
        rfl
  have offeredRaw := offered
  rw [actionEq] at offeredRaw
  have priorActive : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨before.remaining, some who, before.execution⟩) := by
    simpa only [← active] using prior
  obtain ⟨coordinate, request⟩ := onePacket_request_of_nonsilent runtime leaks bounds plan inputs
    horizon scheduler before.remaining who before.execution priorActive priorClear material
      offeredRaw
  have actual := onePacket_event_of_request runtime leaks bounds plan ordered inputs horizon
    scheduler before.remaining who before.execution priorActive coordinate request material
      offeredRaw
  rw [named] at actual
  have eventEq : coordinate.event = event := (Option.some.inj actual).symm
  have coordinateEq : coordinate = ⟨before.execution.application.attempt, event⟩ := by
    cases coordinate with
    | mk attempt selected =>
        have tag := request.1
        cases tag
        cases eventEq
        rfl
  exact ⟨before, prior, isPrefix, active, past, viewed, coordinateEq ▸ request, offered⟩

include ordered in
/-- Distinct chronological binding sends in one physical attempt have strict
source rank order. The firstness guard derives distinctness of events from the
actual earlier emitted packet; no sortedness or unique-record premise is used. -/
theorem recorded_binding_rank_lt {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (earlier : List (app).PlayerEntry) (first : (app).PlayerEntry)
    (middle : List (app).PlayerEntry) (second : (app).PlayerEntry)
    (later : List (app).PlayerEntry)
    (recalled : control.execution.recall who = earlier ++ first :: (middle ++ second :: later))
    (firstMaterial secondMaterial : WitnessedSubmission graph)
    (firstSent : first.action.transmission = some firstMaterial)
    (secondSent : second.action.transmission = some secondMaterial)
    (firstEvent secondEvent : graph.EventId) (firstCandidate secondCandidate : Handle graph)
    (firstNamed : firstMaterial.call.packet = .commitment firstEvent firstCandidate)
    (secondNamed : secondMaterial.call.packet = .commitment secondEvent secondCandidate)
    (sameAttempt : first.beforeView.application.2.attempt =
      second.beforeView.application.2.attempt) :
    firstEvent.val < secondEvent.val := by
  have secondSplit : control.execution.recall who =
      (earlier ++ first :: middle) ++ second :: later := by
    simpa only [List.append_assoc, List.cons_append] using recalled
  obtain ⟨right, rightTrace, rightPrefix, rightActive, rightPast, secondView, secondRequest,
    secondAllowed⟩ := recorded_binding_request runtime leaks bounds plan ordered inputs horizon
      scheduler trace clear who (earlier ++ first :: middle) second later secondSplit secondMaterial
        secondSent secondEvent secondCandidate secondNamed
  have rightClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler right control rightTrace trace rightPrefix clear).1
  obtain ⟨left, leftTrace, leftPrefix, _leftActive, _leftPast, firstView, firstRequest,
    _firstAllowed⟩ := recorded_binding_request runtime leaks bounds plan ordered inputs horizon
      scheduler rightTrace rightClear who earlier first middle rightPast firstMaterial firstSent
        firstEvent firstCandidate firstNamed
  have rightRaw := (menu).toRawTrace initial horizon scheduler rightTrace
  have firstRetained : first ∈ right.execution.recall who := by
    rw [rightPast]
    exact List.mem_append_right earlier List.mem_cons_self
  obtain ⟨message, emitted, _sender, packet⟩ := recalled_submission_emitted runtime leaks initial
    horizon scheduler rightRaw who first firstRetained firstMaterial firstSent
  have ownOutput : message ∈ (app).outputs (right.execution.recall who) :=
    List.mem_filterMap.mpr ⟨first, firstRetained, emitted⟩
  have tag := phase_recalled_emission_attempt runtime leaks initial horizon scheduler rightRaw
    who first firstRetained message emitted
  have currentTag : message.payload.attempt = right.execution.application.attempt := by
    rw [tag, sameAttempt, secondView]
    rfl
  have different : firstEvent ≠ secondEvent := by
    intro sameEvent
    have rightTraceActive : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨right.remaining, some who, right.execution⟩) := by
      simpa only [← rightActive] using rightTrace
    have actionEq : second.action = ⟨some secondMaterial⟩ := by
      cases actionAt : second.action with
      | mk transmission =>
          have actual : transmission = some secondMaterial := by
            simpa only [actionAt] using secondSent
          cases actual
          rfl
    rw [actionEq] at secondAllowed
    have absent := unsent_of_nonsilent runtime leaks bounds plan ordered inputs horizon scheduler
      right.remaining who right.execution rightTraceActive
        ⟨right.execution.application.attempt, secondEvent⟩ secondRequest secondMaterial
          secondAllowed
    apply absent message ownOutput
    simp only [event?, packet, firstNamed, sameEvent, Payload.event?, Option.map_some, currentTag]
  exact phase_ready_owner_rank_lt_of_clear_prefix runtime leaks ordered menu initial horizon
    scheduler left right leftTrace rightTrace leftPrefix rightClear who firstEvent secondEvent
      firstRequest.2.2.2.1 secondRequest.2.2.2.1 firstRequest.2.2.1 secondRequest.2.2.1 different


include ordered in
/-- Every earlier raw binding send in the current attempt strictly precedes
a genuine still-unsent owned request. Readiness supplies weak rank order;
the actual recorded envelope and unsent condition exclude equality. -/
theorem recorded_binding_rank_lt_of_unsent_request {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (earlier : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (later : List (app).PlayerEntry)
    (recalled : control.execution.recall who = earlier ++ entry :: later)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (event : graph.EventId) (candidate : Handle graph)
    (named : material.call.packet = .commitment event candidate)
    (sameAttempt : entry.beforeView.application.2.attempt = control.execution.application.attempt)
    (selected : graph.EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, selected⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩) :
    event.val < selected.val := by
  obtain ⟨before, prior, isPrefix, _active, _past, _viewed, previousRequest, _allowed⟩ :=
    recorded_binding_request runtime leaks bounds plan ordered inputs horizon scheduler trace clear
      who earlier entry later recalled material transmitted event candidate named
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have retained : entry ∈ control.execution.recall who := by
    rw [recalled]
    exact List.mem_append_right earlier List.mem_cons_self
  obtain ⟨message, emitted, _sender, packet⟩ := recalled_submission_emitted runtime leaks initial
    horizon scheduler raw who entry retained material transmitted
  have ownOutput : message ∈ (app).outputs (control.execution.recall who) :=
    List.mem_filterMap.mpr ⟨entry, retained, emitted⟩
  have tag := phase_recalled_emission_attempt runtime leaks initial horizon scheduler raw who entry
    retained message emitted
  have currentTag := tag.trans sameAttempt
  have different : event ≠ selected := by
    intro same
    apply unsent message ownOutput
    simp only [event?, packet, named, same, Payload.event?, Option.map_some, currentTag]
  exact phase_ready_owner_rank_lt_of_clear_prefix runtime leaks ordered menu initial horizon
    scheduler before control prior trace isPrefix clear who event selected previousRequest.2.2.2.1
      request.2.2.2.1 previousRequest.2.2.1 request.2.2.1 different

end Vegas.EventGraphRuntime.PhaseCount
