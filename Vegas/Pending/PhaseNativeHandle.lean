/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeResponse
import Vegas.Pending.PhaseReadyRequests

/-! # Actual clear packet inclusions retain the original native handler -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- An actual accepted phase edge whose endpoint is clear has exactly its raw
native result. Normalization contributes no semantic completion or rollback. -/
theorem handle_native_of_clear_result (state next : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next)
    (clear : next.current.excluded = ∅) :
    (N).handle state.current.native (Message.mapPayload CommitAttemptPacket.packet message) =
      some next.current.native := by
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · rename_i gate
    obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have phaseToken := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp gate).1).1
    have token := (Bool.and_eq_true_iff.mp phaseToken).2
    rw [reactiveApplication_handle_of_tokenValid runtime (nativeLeaks leaks plan) _ _ token]
    change runtime.handle state.current.native
      ⟨message.id, message.payload.packet.call⟩ = _
    rw [rawAccepted]
    apply congrArg some
    exact (congrArg RecoveryState.native
      (PhaseRuntimeState.normalize_of_clear _ clear).1).symm
  · cases accepted

/-- An accepting native call from an actual clear counted input has the current
static phase address. Old-phase packets cannot regain acceptance after erasure. -/
theorem handle_of_native_accepted [Fintype Player] (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph))
    (authentic : message ∈ current.execution.network.inputs) (native : State graph)
    (accepted : (N).handle current.execution.application.current.native
      (Message.mapPayload CommitAttemptPacket.packet message) = some native) :
    current.execution.application.handle runtime message =
      some (({ current.execution.application with current :=
        current.execution.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize) := by
  let state : PhaseRuntimeState graph := current.execution.application
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler
    trace
  obtain ⟨token, rawAccepted⟩ := reactiveApplication_handle_eq_some runtime (nativeLeaks leaks plan)
    state.current.native native (Message.mapPayload CommitAttemptPacket.packet message) accepted
  change message.payload.packet.tokenValid = true at token
  change runtime.handle state.current.native
    ⟨message.id, message.payload.packet.call⟩ = some native at rawAccepted
  obtain ⟨event, named, ready, _action, _supported⟩ :=
    handle_config_mem_step runtime state.current.native native _ rawAccepted
  change message.payload.packet.call.event? graph = some event at named
  have frontier := (phaseApplication_live runtime leaks).history _ horizon scheduler
    (fun initial supported => by
      obtain ⟨input, _support, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan input,
        PhaseRuntimeState.initial_live plan input⟩) rawTrace
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler rawTrace
  have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
    rawTrace
  obtain ⟨phase, head, inside⟩ := state.ready_current_phase ordered frontier.1 frontier.2
    geometry.2.2 event ready
  change state.phases.head? = some phase at head
  have member : phase ∈ plan.phases := suffix.subset (List.mem_of_mem_head? head)
  have static := plan.eventPhase_of_mem phase member event inside
  have generation := (phase_clear_history runtime leaks plan inputs horizon scheduler current
    rawTrace clear).1
  change state.generation = 0 at generation
  have stateAttempt : state.attempt = ⟨phase.low, 0⟩ := by
    simp only [PhaseRuntimeState.attempt, head, Option.map_some, Option.getD_some, generation]
  have recovered := PhaseCount.stamp_nativeMessage_of_clear runtime leaks plan bounds inputs
    horizon scheduler trace clear message authentic
  have restored : plan.stampPacket message.payload.packet =
      ⟨state.attempt, message.payload.packet⟩ := by
    simp only [RuntimePhasePlan.stampPacket, named, Option.map_some, Option.getD_some,
      static, stateAttempt]
  have currentAttempt : message.payload.attempt = state.attempt :=
    (congrArg CommitAttemptPacket.attempt recovered).symm.trans
      (congrArg CommitAttemptPacket.attempt restored)
  have allowed : state.allows message.payload.packet.call = true := by
    simp only [PhaseRuntimeState.allows, head, named, inside, decide_true]
  have unexcluded : state.current.excludedCall message.payload.packet.call = false := by
    change state.current.excluded = ∅ at clear
    simp only [RecoveryState.excludedCall, named, RecoveryState.excludedEvent]
    cases graph.actor? event <;> simp [clear]
  change state.handle runtime message = _
  simp only [PhaseRuntimeState.handle, CommitAttemptPacket.tokenValid, currentAttempt,
    decide_true, token, Bool.true_and, allowed, unexcluded, Bool.not_false, ↓reduceIte,
    rawAccepted, Option.map_some]
  rfl

/-- Erasing an authentic counted packet commutes with the complete handler law;
phase normalization remains explicit on its accepted native result. -/
theorem handle_map_of_clear [Fintype Player] (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph))
    (authentic : message ∈ current.execution.network.inputs) :
    current.execution.application.handle runtime message =
      ((N).handle current.execution.application.current.native
        (Message.mapPayload CommitAttemptPacket.packet message)).map fun native =>
          ({ current.execution.application with
            current := current.execution.application.current.inclusionResult
              message.payload.packet.call native } : PhaseRuntimeState graph).normalize := by
  cases accepted : (N).handle current.execution.application.current.native
      (Message.mapPayload CommitAttemptPacket.packet message) with
  | some native =>
      exact handle_of_native_accepted runtime leaks plan bounds ordered maximal inputs horizon
        scheduler trace clear message authentic native accepted
  | none =>
      simp only [Option.map_none]
      unfold PhaseRuntimeState.handle
      split
      · rename_i gate
        have phaseToken := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp gate).1).1
        have token := (Bool.and_eq_true_iff.mp phaseToken).2
        rw [reactiveApplication_handle_of_tokenValid runtime (nativeLeaks leaks plan) _ _ token]
          at accepted
        change runtime.handle current.execution.application.current.native
          ⟨message.id, message.payload.packet.call⟩ = none at accepted
        rw [accepted, Option.map_none]
      · rfl

end Vegas.EventGraphRuntime.PhaseNativeProjection
