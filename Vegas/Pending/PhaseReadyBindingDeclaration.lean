/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingResponseOrigin
import Vegas.Pending.PhaseReceiptOrder
import Vegas.Pending.CompletedBindingReadback
import Vegas.Pending.PhaseCompletedBindingMeaning

/-! # Actual earlier declarations at a surviving owner's ready binding -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

/-- Readiness and survival derive an earlier owned binding's accepted handle
and its exact typed store cell, even after other owners have failed. -/
theorem phase_ready_earlier_binding_read
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (ordered : graph.RevealRelaxedOrdered)
    (phase : RuntimePhase graph)
    (installed : control.execution.application.phases.head? = some phase)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (active : owner ∉ control.execution.application.current.excluded)
    (earlier : graph.EventId) (priorPayload : L.Ty)
    (priorBinding : graph.outputLayout earlier = .binding owner priorPayload)
    (inside : earlier ∈ phase.events) (before : earlier.val < event.val) :
    ∃ candidate : Handle graph, candidate.1 = owner ∧
      control.execution.application.current.native.accepted (.inr earlier) = some candidate ∧
      (⟨.inr earlier, priorBinding⟩ : FieldRef graph.layout (.binding owner priorPayload)).get?
          control.execution.application.current.native.config.store =
        some (control.execution.application.current.native.bindingResult candidate priorPayload) :=
    by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have exclusions := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler raw
  have receipts := (exclusions.installed phase installed).ready_binding_receipts ordered event
    ready owner payload binding active
  have present := receipts.2 earlier ((phase.mem_events earlier).mp inside).1 before
    priorPayload priorBinding
  obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
  have records :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  obtain ⟨_otherPayload, typed⟩ := records.accepted_typed (.inr earlier) candidate accepted
  have owned : candidate.1 = owner :=
    (EventField.binding.inj (typed.symm.trans priorBinding)).1
  have dependency : earlier ∈ graph.order.predecessors event :=
    ordered.keeps (barrierOrder_same_owner graph.outputLayout before (by
      rw [priorBinding, binding]
      rfl)) (Or.inl (by simp only [priorBinding, EventField.IsPublication, not_false_eq_true]))
  have read := records.binding_read
    (⟨.inr earlier, priorBinding⟩ : FieldRef graph.layout (.binding owner priorPayload))
      earlier rfl (ready.2 dependency)
  exact ⟨candidate, owned, accepted, by simpa only [accepted, Option.elim_some] using read⟩

/-- The earlier private value read at a genuine ready binding comes from a
remembered supported SEND at its own original callback and full attempt.
No accepted-handle, clear-state or desired declaration premise is supplied. -/
theorem phase_ready_earlier_binding_declaration
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (ordered : graph.RevealRelaxedOrdered)
    (phase : RuntimePhase graph)
    (installed : control.execution.application.phases.head? = some phase)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (active : owner ∉ control.execution.application.current.excluded)
    (earlier : graph.EventId) (priorPayload : L.Ty)
    (priorBinding : graph.outputLayout earlier = .binding owner priorPayload)
    (inside : earlier ∈ phase.events) (earlierRank : earlier.val < event.val)
    (policy : (app).Policy) (consistent : policy.Consistent (control.execution.recall owner)) :
    ∃ (candidate : Handle graph) (message : Message Player (CommitAttemptPacket graph))
      (entry : (app).PlayerEntry) (material : WitnessedSubmission graph)
      (before : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some before)),
      candidate.1 = owner ∧
      control.execution.application.current.native.accepted (.inr earlier) = some candidate ∧
      (⟨.inr earlier, priorBinding⟩ : FieldRef graph.layout (.binding owner priorPayload)).get?
          control.execution.application.current.native.config.store =
        some (control.execution.application.current.native.bindingResult candidate priorPayload) ∧
      message.sender = owner ∧
      message.payload.attempt = control.execution.application.attempt ∧
      message.payload.packet.call = .commitment earlier candidate ∧
      entry ∈ control.execution.recall owner ∧ entry.emitted = some message ∧
      entry.action.transmission = some material ∧
      material.call.packet = .commitment earlier candidate ∧
      TracePrefix prior trace ∧
      before.execution.application.attempt = control.execution.application.attempt ∧
      before.actor = some owner ∧
      entry.beforeView = before.execution.observe (app) owner ∧
      entry.action ∈ (policy (before.execution.recall owner)
        (before.execution.observe (app) owner)).support ∧
      ∃ suffix, control.execution.recall owner =
        before.execution.recall owner ++ entry :: suffix := by
  obtain ⟨candidate, owned, accepted, read⟩ :=
    phase_ready_earlier_binding_read runtime leaks bounds plan inputs horizon scheduler trace
      ordered phase installed owner event payload binding ready active earlier priorPayload
        priorBinding inside earlierRank
  have recalled : policy.Consistent (control.execution.recall candidate.1) := by
    simpa only [owned] using consistent
  obtain ⟨message, entry, material, before, prior, sender, attempt, call, retained, emitted,
    sent, named, isPrefix, sameAttempt, acting, viewed, supported, suffix⟩ :=
    phase_accepted_binding_response_origin runtime leaks bounds plan inputs horizon scheduler trace
      earlier candidate accepted phase installed inside policy recalled
  rw [owned] at retained acting viewed supported suffix
  exact ⟨candidate, message, entry, material, before, prior, owned, accepted, read,
    sender.trans owned, attempt, call, retained, emitted, sent, named, isPrefix, sameAttempt,
    acting, viewed, supported, suffix⟩

/-- A surviving completed binding's current typed store is its original
remembered declaration, through arbitrary foreign exclusions. Freshness is
derived by the existing actual-declaration theorem. -/
theorem phase_completed_recorded_binding_read
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (lower : control.execution.application.attempt.phase ≤ event.val)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed)
    (surviving : owner ∉ control.execution.application.current.excluded)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (entry : (app).PlayerEntry)
    (recorded : entry ∈ control.execution.recall owner)
    (declared : entry.action = phaseBindingResponse runtime leaks owner event payload result serial)
    (sameAttempt : entry.beforeView.application.2.attempt =
      control.execution.application.attempt) :
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get?
      control.execution.application.current.native.config.store = some result := by
  obtain ⟨original, retained, meaning⟩ := PhaseCount.completed_recorded_binding_action
    runtime leaks bounds plan inputs horizon scheduler trace owner event payload binding lower
      completed surviving result serial entry recorded declared sameAttempt
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨_draw, valid⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler raw
  have bindings :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  have exactMeaning := bindings.recorded_binding_action valid.active.reachable event owner payload
    binding original retained
  have read := bindings.binding_read
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)) event rfl completed
  rw [← exactMeaning, meaning] at read
  exact read

end Vegas.EventGraphRuntime
