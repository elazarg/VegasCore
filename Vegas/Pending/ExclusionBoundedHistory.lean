/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedRoundTrip
import Vegas.Pending.ExclusionClearReach
import Interaction.ReactiveResponseBelief

/-! # Actual finite one-packet histories before public exclusion

Uniform reference laws, exact raw reach weights, and the existing menu embedding
supply finite preimages of the clear raw-history bijection. The statements concern
entire realized histories and require no positive reach or profile hypothesis.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (RecoveryState graph))
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
  (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeMenu" => MessageBounds.onePacketMenu runtime leaks bounds
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NativeModel" => ReactiveApplication.ResponseMenu.information
  (NativeMenu) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.ResponseMenu.information
  (RecoveryMenu) initial horizon scheduler
local notation "NativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (NativeMenu) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryProtocol" => ReactiveApplication.ResponseMenu.protocol
  (RecoveryMenu) initial horizon scheduler
local notation "NativeRaw" => ReactiveApplication.information
  (reactiveApplication runtime leaks) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryRaw" => ReactiveApplication.information
  (recoveryApplication runtime leaks) initial horizon scheduler

/-- Every publicly clear native one-packet history has an actual recovery
one-packet lift with exactly the complete raw lifted history. -/
theorem exists_recoveryBoundedHistory
    (history : (NativeProtocol).History)
    (clear : ∀ current, history.state = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)) :
    ∃ lifted : (RecoveryProtocol).History,
      (RecoveryMenu).toRawHistory initial horizon scheduler lifted =
        recoveryHistory runtime leaks initial initialized horizon scheduler
          ((NativeMenu).toRawHistory (initial.map RecoveryState.native) horizon
            (nativeScheduler runtime leaks scheduler) history) clear := by
  classical
  let reference := (NativeMenu).uniformPolicy (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler)
  let recovery := boundedRecoveryProfile runtime leaks bounds initial horizon scheduler reference
  let embedded := fun who => (RecoveryMenu).embedPolicy initial horizon scheduler who (recovery who)
  let raw := (NativeMenu).toRawHistory (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler) history
  let lifted := recoveryHistory runtime leaks initial initialized horizon scheduler raw clear
  have profiles : nativeProfile runtime leaks initial horizon scheduler embedded =
      fun who => (NativeMenu).embedPolicy (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) who (reference who) := by
    funext who
    have same := boundedNativeProfile_embed runtime leaks bounds initial horizon scheduler
      recovery who
    have roundtrip := boundedNativeProfile_boundedRecoveryProfile runtime leaks bounds initial
      horizon scheduler reference
    change boundedNativeProfile runtime leaks bounds initial horizon scheduler recovery = reference
      at roundtrip
    rw [roundtrip] at same
    exact same.symm
  have nativePositive : 0 < (NativeRaw).historyReachWeight
      (fun who => (NativeMenu).embedPolicy (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) who (reference who)) raw := by
    rw [(NativeMenu).historyReachWeight_toRawHistory]
    exact (NativeModel).historyReachWeight_pos_of_fullSupport reference
      ((NativeMenu).uniform_fullyMixed (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler)) history
  have positive : 0 < (RecoveryRaw).historyReachWeight embedded lifted := by
    rw [historyReachWeight_recoveryHistory runtime leaks initial initialized horizon scheduler
      embedded raw.trace clear, profiles]
    exact nativePositive
  have supported : lifted ∈ ((RecoveryRaw).runBehavioral embedded lifted.trace.length).support :=
    (PMF.apply_pos_iff _ _).mp positive
  rw [← (RecoveryMenu).runBehavioral_embed initial horizon scheduler recovery lifted.trace.length,
    PMF.mem_support_map_iff] at supported
  obtain ⟨finiteHistory, _supported, same⟩ := supported
  exact ⟨finiteHistory, same⟩

include initialized in
/-- Every clear actual recovery one-packet history has an actual native
one-packet projection with exactly its complete raw projected history. -/
theorem exists_nativeBoundedHistory
    (history : (RecoveryProtocol).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    ∃ projected : (NativeProtocol).History,
      (NativeMenu).toRawHistory (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) projected =
        nativeHistory runtime leaks initial horizon scheduler
          ((RecoveryMenu).toRawHistory initial horizon scheduler history) clear := by
  classical
  let reference := (RecoveryMenu).uniformPolicy initial horizon scheduler
  let projected := boundedNativeProfile runtime leaks bounds initial horizon scheduler reference
  let embedded := fun who =>
    (RecoveryMenu).embedPolicy initial horizon scheduler who (reference who)
  let raw := (RecoveryMenu).toRawHistory initial horizon scheduler history
  let image := nativeHistory runtime leaks initial horizon scheduler raw clear
  have profiles : (fun who => (NativeMenu).embedPolicy (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler) who (projected who)) =
      nativeProfile runtime leaks initial horizon scheduler embedded := by
    funext who
    exact boundedNativeProfile_embed runtime leaks bounds initial horizon scheduler reference who
  have recoveryPositive : 0 < (RecoveryRaw).historyReachWeight embedded raw := by
    rw [(RecoveryMenu).historyReachWeight_toRawHistory]
    exact (RecoveryModel).historyReachWeight_pos_of_fullSupport reference
      ((RecoveryMenu).uniform_fullyMixed initial horizon scheduler) history
  have positive : 0 < (NativeRaw).historyReachWeight
      (fun who => (NativeMenu).embedPolicy (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) who (projected who)) image := by
    rw [profiles, ← historyReachWeight_nativeHistory runtime leaks initial initialized horizon
      scheduler embedded raw clear]
    exact recoveryPositive
  have supported : image ∈ ((NativeRaw).runBehavioral
      (fun who => (NativeMenu).embedPolicy (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) who (projected who))
      image.trace.length).support :=
    (PMF.apply_pos_iff _ _).mp positive
  rw [← (NativeMenu).runBehavioral_embed (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler) projected image.trace.length,
    PMF.mem_support_map_iff] at supported
  obtain ⟨finiteHistory, _supported, same⟩ := supported
  exact ⟨finiteHistory, same⟩

end Vegas.EventGraphRuntime.RecoveryProjection
