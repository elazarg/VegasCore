/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionStoppedLaw
import Interaction.ReactiveResponseStopped

/-! # First-exclusion laws for actual response menus

Restricting the recovery policies to any response menu retains the exact native
comparison law of surviving histories and first excluded-owner labels.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (RecoveryState graph)) (horizon : Nat)
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeModel" => ReactiveApplication.information (reactiveApplication runtime leaks)
  (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.information
  (recoveryApplication runtime leaks) initial horizon scheduler
local notation "NativeProtocol" => ReactiveApplication.protocol (reactiveApplication runtime leaks)
  (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
local notation "RecoveryProtocol" => ReactiveApplication.protocol
  (recoveryApplication runtime leaks) initial horizon scheduler

/-- The actual finite-menu continuation has the native classified stopped law,
including corresponding additional stopping conditions while publicly clear. -/
theorem responseMenu_exclusion_or_classified_eq
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (menu : (runtime.recoveryApplication leaks).ResponseMenu)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (nativeCertificate : (NativeProtocol).WellFoundedHistories)
    (recoveryCertificate : (RecoveryProtocol).WellFoundedHistories)
    (menuCertificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (nativeStop : (NativeProtocol).History → Prop)
    (recoveryStop : (RecoveryProtocol).History → Prop)
    (stopAgrees : ∀ history (clear : RecoveryClear runtime leaks initial horizon scheduler history),
      nativeStop (nativeHistory runtime leaks initial horizon scheduler history clear) ↔
        recoveryStop history)
    (history : (menu.protocol initial horizon scheduler).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    let raw := menu.toRawHistory initial horizon scheduler history
    ((NativeModel).runBehavioralUntil nativeCertificate
      (nativeProfile runtime leaks initial horizon scheduler
        (fun who => menu.embedPolicy initial horizon scheduler who (profile who)))
      (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history ∨
        nativeStop history)
      (nativeHistory runtime leaks initial horizon scheduler raw clear)).map
        (nativeClassifiedReadout runtime leaks initial horizon scheduler) =
    ((menu.information initial horizon scheduler).runBehavioralUntil menuCertificate profile
      (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler
        (menu.toRawHistory initial horizon scheduler history) ∨
        recoveryStop (menu.toRawHistory initial horizon scheduler history)) history).map
      (fun history => recoveryClassifiedReadout runtime leaks initial horizon scheduler
        (menu.toRawHistory initial horizon scheduler history)) := by
  intro raw
  have compared := runBehavioralUntil_exclusion_or_classified_eq runtime leaks initial horizon
    scheduler initialized (fun who => menu.embedPolicy initial horizon scheduler who (profile who))
    nativeCertificate recoveryCertificate nativeStop recoveryStop stopAgrees raw clear
  rw [← menu.runBehavioralUntil_embed initial horizon scheduler recoveryCertificate menuCertificate
    profile (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history ∨
      recoveryStop history) history,
    PMF.map_comp] at compared
  exact compared

end Vegas.EventGraphRuntime.RecoveryProjection
