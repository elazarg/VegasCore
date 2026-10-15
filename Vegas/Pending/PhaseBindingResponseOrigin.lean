/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.PhaseBindingStampHistory
import Vegas.Pending.PhaseOwnCommitments
import Interaction.ReactiveRecordedResponse
import Interaction.ReactiveTrafficIdentity

/-! # Actual supported callback origins of surviving accepted bindings -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A native accepted handle stamped by a real history retains its original
supported callback, even before physical phase normalization. -/
theorem phase_binding_response_origin_of_stamp (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (native : State graph)
    (stamped : BindingStamp (fun who => (app).outputs (control.execution.recall who))
      control.execution.application.attempt native)
    (event : graph.EventId) (candidate : Handle graph)
    (accepted : native.accepted (.inr event) = some candidate)
    (lower : control.execution.application.attempt.phase ≤ event.val)
    (policy : (app).Policy)
    (consistent : policy.Consistent (control.execution.recall candidate.1)) :
    ∃ (message : Message Player (CommitAttemptPacket graph))
      (entry : (app).PlayerEntry) (material : WitnessedSubmission graph)
      (before : (app).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before)),
      message.sender = candidate.1 ∧
      message.payload.attempt = control.execution.application.attempt ∧
      message.payload.packet.call = .commitment event candidate ∧
      entry ∈ control.execution.recall candidate.1 ∧ entry.emitted = some message ∧
      entry.action.transmission = some material ∧
      material.call.packet = .commitment event candidate ∧
      TracePrefix prior trace ∧
      before.execution.application.attempt = control.execution.application.attempt ∧
      before.actor = some candidate.1 ∧
      entry.beforeView = before.execution.observe (app) candidate.1 ∧
      entry.action ∈ (policy (before.execution.recall candidate.1)
        (before.execution.observe (app) candidate.1)).support ∧
      ∃ suffix, control.execution.recall candidate.1 =
        before.execution.recall candidate.1 ++ entry :: suffix := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  rcases stamped event candidate accepted with earlier |
      ⟨message, authored, sender, call, attempt⟩
  · omega
  · have recalled := (app).history_inputRecall _ horizon scheduler raw
    change control.execution.InputRecall (app) at recalled
    change message ∈ (app).outputs (control.execution.recall candidate.1) at authored
    have input : message ∈ control.execution.network.inputs := by
      rw [← recalled candidate.1] at authored
      exact (List.mem_filter.mp authored).1
    have issued := ((app).history_provenance _ horizon scheduler raw).inputs message input
    obtain ⟨entry, retained, material, transmitted, emitted, state, known, packet⟩ := issued
    rw [sender] at retained
    have materialCall : material.call.packet = .commitment event candidate := by
      have exactCall := phase_emit_call state message.sender known material
      change state.emit message.sender known material = message.payload at packet
      exact exactCall.symm.trans ((congrArg (fun output => output.packet.call) packet).trans call)
    obtain ⟨before, prior, retainedTrace, acting, viewed, supported, suffix, samePast⟩ :=
      (PhaseCount.onePacketMenu runtime leaks bounds).recorded_response_supported _ horizon
        scheduler control trace candidate.1 policy consistent entry retained
    have authoredAttempt := phase_recalled_emission_attempt runtime leaks _ horizon scheduler
      raw candidate.1 entry retained message emitted
    rw [viewed] at authoredAttempt
    have sameAttempt : before.execution.application.attempt =
        control.execution.application.attempt := authoredAttempt.symm.trans attempt
    exact ⟨message, entry, material, before, prior, sender, attempt, call, retained, emitted,
      transmitted, materialCall, retainedTrace, sameAttempt, acting, viewed, supported, suffix,
        samePast⟩

/-- A surviving current-phase accepted handle was authored at a true earlier
active callback of this same full history, with positive original policy mass.
The permanent packet, its original submission material and full recall prefix
are retained, rather than replacing the callback by a new source sample. -/
theorem phase_accepted_binding_response_origin (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (event : graph.EventId) (candidate : Handle graph)
    (accepted : control.execution.application.current.native.accepted (.inr event) =
      some candidate)
    (phase : RuntimePhase graph) (installed : control.execution.application.phases.head? =
      some phase) (inside : event ∈ phase.events) (policy : (app).Policy)
    (consistent : policy.Consistent (control.execution.recall candidate.1)) :
    ∃ (message : Message Player (CommitAttemptPacket graph))
      (entry : (app).PlayerEntry) (material : WitnessedSubmission graph)
      (before : (app).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before)),
      message.sender = candidate.1 ∧
      message.payload.attempt = control.execution.application.attempt ∧
      message.payload.packet.call = .commitment event candidate ∧
      entry ∈ control.execution.recall candidate.1 ∧ entry.emitted = some message ∧
      entry.action.transmission = some material ∧
      material.call.packet = .commitment event candidate ∧
      TracePrefix prior trace ∧
      before.execution.application.attempt = control.execution.application.attempt ∧
      before.actor = some candidate.1 ∧
      entry.beforeView = before.execution.observe (app) candidate.1 ∧
      entry.action ∈ (policy (before.execution.recall candidate.1)
        (before.execution.observe (app) candidate.1)).support ∧
      ∃ suffix, control.execution.recall candidate.1 =
        before.execution.recall candidate.1 ++ entry :: suffix := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
  have lower := ((phase.mem_events event).mp inside).1
  have address : control.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  rw [← address] at lower
  exact phase_binding_response_origin_of_stamp runtime leaks bounds plan inputs horizon scheduler
    trace control.execution.application.current.native stamped event candidate accepted lower
      policy consistent

end Vegas.EventGraphRuntime
