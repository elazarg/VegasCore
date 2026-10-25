/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseCanonicalTrace
import Vegas.Pending.ExclusionBoundedHistory

/-! # Actual native counted prefixes from clear canonical phase traces

The clear recovery trace is constructed from the phase trace, then the existing
bounded recovery/native correspondence produces a genuine native counted prefix.
The complete projected endpoint, length and absence of public failures are retained.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))

local notation "plan" => sequentialRuntimePhasePlan program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "N" => reactiveApplication runtime recoveryLeaks
local notation "normal" => PhaseCount.normalization runtime leaks
local notation "canonical" => ReactiveApplication.SubmissionNormalization.menu (normal)
  (PhaseCount.onePacketMenu runtime leaks bounds)
local notation "projection" => protocolState runtime leaks recoveryLeaks
local notation "recoveryScheduler" =>
  SequentialPhaseSchedulerInformation.scheduler program runtime leaks recoveryLeaks
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan)
local notation "recoveryInitial" =>
  PMF.map (fun input => RecoveryState.mk (State.initial input) ∅)
local notation "old" => Recovery.onePacketMenu runtime recoveryLeaks bounds
local notation "nativeMenu" => MessageBounds.onePacketMenu runtime recoveryLeaks bounds

/-- Every canonical clear phase prefix yields an actual native counted prefix
with its complete projected current state and original player recalls. -/
theorem exists_native_canonical_clear_history
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {state : (P).ProtocolState}
    (trace : ((canonical).protocol (phaseInitial inputs) horizon scheduler).Trace state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
        state.current.excluded = ∅) state) :
    ∃ native : ((nativeMenu).protocol ((recoveryInitial inputs).map RecoveryState.native) horizon
        (RecoveryProjection.nativeScheduler runtime recoveryLeaks
          (recoveryScheduler scheduler))).History,
      native.state = RecoveryProjection.protocolState runtime recoveryLeaks (projection state) ∧
      native.trace.length = trace.length ∧
      ∀ current, native.state = some current →
        ExclusionEvidence 0 ∅ (⟨current.execution.application, ∅⟩ : RecoveryState _) := by
  obtain ⟨oldTrace, oldLength⟩ := trace_projected_canonical_clear program runtime leaks bounds
    inputs
    horizon scheduler trace clear
  let oldHistory : ((old).protocol (recoveryInitial inputs) horizon
      (recoveryScheduler scheduler)).History := ⟨projection state, oldTrace⟩
  let rawOldTrace := (old).toRawTrace (recoveryInitial inputs) horizon (recoveryScheduler scheduler)
    oldTrace
  have oldClear : ∀ current, projection state = some current →
      current.execution.application.excluded = ∅ := by
    intro current same
    cases state with
    | none => cases same
    | some before =>
        change some (control runtime leaks recoveryLeaks before) = some current at same
        cases Option.some.inj same
        exact clear
  have initialized : ∀ value ∈ (recoveryInitial inputs).support, ∃ draw,
      value = (⟨State.initial draw, ∅⟩ : RecoveryState _) := by
    intro value supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact ⟨draw, rfl⟩
  obtain ⟨native, rawEq⟩ := RecoveryProjection.exists_nativeBoundedHistory runtime recoveryLeaks
    bounds (recoveryInitial inputs) initialized horizon (recoveryScheduler scheduler) oldHistory
    oldClear
  have endpoint := congrArg (fun history : ((N).protocol
      ((recoveryInitial inputs).map RecoveryState.native) horizon
      (RecoveryProjection.nativeScheduler runtime recoveryLeaks
          (recoveryScheduler scheduler))).History => history.state) rawEq
  change native.state = RecoveryProjection.protocolState runtime recoveryLeaks (projection state)
    at endpoint
  have nativeLength : ∀ {source}
      (prior : ((R).protocol (recoveryInitial inputs) horizon
        (recoveryScheduler scheduler)).Trace source)
      (clear : ∀ current, source = some current → current.execution.application.excluded = ∅),
      (RecoveryProjection.nativeTrace runtime recoveryLeaks (recoveryInitial inputs) horizon
        (recoveryScheduler scheduler) prior clear).length = prior.length := by
    intro source prior
    induction prior with
    | start => intro _clear; rfl
    | extend previous joint legal reached ih =>
        intro clear
        exact congrArg Nat.succ (ih _)
  have length := congrArg (fun history : ((N).protocol
      ((recoveryInitial inputs).map RecoveryState.native) horizon
      (RecoveryProjection.nativeScheduler runtime recoveryLeaks
          (recoveryScheduler scheduler))).History => history.trace.length) rawEq
  change ((nativeMenu).toRawTrace _ _ _ native.trace).length =
    (RecoveryProjection.nativeTrace runtime recoveryLeaks (recoveryInitial inputs) horizon
      (recoveryScheduler scheduler) rawOldTrace oldClear).length at length
  rw [(nativeMenu).toRawTrace_length, nativeLength, (old).toRawTrace_length] at length
  refine ⟨native, endpoint, length.trans oldLength, ?_⟩
  intro current same
  exact RecoveryProjection.nativeHistory_record runtime recoveryLeaks (recoveryInitial inputs)
    initialized horizon (recoveryScheduler scheduler) rawOldTrace oldClear current
      (endpoint.symm.trans same)

end Vegas.EventGraphRuntime.PhaseRecoveryProjection
