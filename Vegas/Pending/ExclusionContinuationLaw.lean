/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionStoppedLaw
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Continuation error bounded by the actual first-exclusion probability -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

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

omit [Fintype Player] in
private theorem nativeStoppedReadout_mass_le (law : PMF (NativeProtocol).History)
    (history : (NativeProtocol).History) :
    (law.map (nativeStoppedReadout runtime leaks initial horizon scheduler)) (some history) ≤
      law history := by
  classical
  rw [PMF.map_apply, tsum_eq_single history]
  · split_ifs <;> simp
  · intro other different
    have unequal : some history ≠ nativeStoppedReadout runtime leaks initial horizon scheduler
        other := by
      unfold nativeStoppedReadout
      split_ifs
      · exact fun same => different (Option.some.inj same).symm
      · exact Option.some_ne_none _
    simp only [unequal, ↓reduceIte]

/-- Any terminal readouts agreeing before exclusion differ by at most the
actual probability of reaching the first-exclusion boundary. No native service
contract or agreement after exclusion is required. -/
theorem terminal_readout_withinTV_of_exclusion
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (nativeCertificate : (NativeProtocol).WellFoundedHistories)
    (recoveryCertificate : (RecoveryProtocol).WellFoundedHistories)
    {Outcome : Type} (nativeReadout : (NativeProtocol).History → Outcome)
    (recoveryReadout : (RecoveryProtocol).History → Outcome)
    (agree : ∀ history (clear : RecoveryClear runtime leaks initial horizon scheduler history),
      recoveryReadout history = nativeReadout
        (nativeHistory runtime leaks initial horizon scheduler history clear))
    (history : (RecoveryProtocol).History)
    (clear : RecoveryClear runtime leaks initial horizon scheduler history) :
    let recoveryStopped := (RecoveryModel).runBehavioralUntil recoveryCertificate profile
      (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history) history
    PMF.WithinTV (((recoveryStopped.map
      (recoveryStoppedReadout runtime leaks initial horizon scheduler)) none).toReal)
      (((RecoveryModel).runBehavioralTerminalFrom recoveryCertificate profile history).map
        recoveryReadout)
      (((NativeModel).runBehavioralTerminalFrom nativeCertificate
        (nativeProfile runtime leaks initial horizon scheduler profile)
        (nativeHistory runtime leaks initial horizon scheduler history clear)).map nativeReadout) :=
    by
  classical
  intro recoveryStopped
  let native := nativeHistory runtime leaks initial horizon scheduler history clear
  let nativeStopped := (NativeModel).runBehavioralUntil nativeCertificate
    (nativeProfile runtime leaks initial horizon scheduler profile)
    (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history) native
  have stoppedLaw := runBehavioralUntil_exclusion_map_eq runtime leaks initial horizon scheduler
    initialized profile nativeCertificate recoveryCertificate history clear
  have dominated : ∀ target,
      (recoveryStopped.map (recoveryStoppedReadout runtime leaks initial horizon scheduler))
        (some target) ≤ nativeStopped target := by
    intro target
    rw [← stoppedLaw]
    exact nativeStoppedReadout_mass_le runtime leaks initial horizon scheduler nativeStopped target
  let first := fun start : (RecoveryProtocol).History =>
    ((RecoveryModel).runBehavioralTerminalFrom recoveryCertificate profile start).map
      recoveryReadout
  let second := fun start : (NativeProtocol).History =>
    ((NativeModel).runBehavioralTerminalFrom nativeCertificate
      (nativeProfile runtime leaks initial horizon scheduler profile) start).map nativeReadout
  have close := PMF.WithinTV.bind_of_dominated recoveryStopped nativeStopped
    (recoveryStoppedReadout runtime leaks initial horizon scheduler) dominated first second
    (fun _ => 0) (fun _ => le_rfl) (fun _ => zero_le_one) (by
      intro stop supported target decoded
      unfold recoveryStoppedReadout at decoded
      split_ifs at decoded with clearStop
      · cases Option.some.inj decoded
        have ended : (RecoveryProtocol).terminal stop.state := by
          rcases (RecoveryModel).mem_support_runBehavioralUntil recoveryCertificate profile
            (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history)
            history stop supported with excluded | ended
          · exact (excluded clearStop).elim
          · exact ended
        have nativeEnded : (NativeProtocol).terminal
            (nativeHistory runtime leaks initial horizon scheduler stop clearStop).state :=
          (terminal_protocolState runtime leaks stop.state).mpr ended
        have same : first stop = second
            (nativeHistory runtime leaks initial horizon scheduler stop clearStop) := by
          dsimp only [first, second]
          simp only [InformationModel.runBehavioralTerminalFrom,
            (RecoveryProtocol).randomizedBackwardLaw_of_terminal (history := stop) ended,
            (NativeProtocol).randomizedBackwardLaw_of_terminal
              (history := nativeHistory runtime leaks initial horizon scheduler stop clearStop)
              nativeEnded,
            PMF.pure_map, agree stop clearStop]
        rw [same]
        exact PMF.WithinTV.refl _
      )
  have firstLaw : recoveryStopped.bind first =
      ((RecoveryModel).runBehavioralTerminalFrom recoveryCertificate profile history).map
        recoveryReadout := by
    rw [(RecoveryModel).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil recoveryCertificate
      profile (fun history => ¬ RecoveryClear runtime leaks initial horizon scheduler history)
      history, PMF.map_bind]
  have secondLaw : nativeStopped.bind second =
      ((NativeModel).runBehavioralTerminalFrom nativeCertificate
        (nativeProfile runtime leaks initial horizon scheduler profile) native).map nativeReadout :=
      by
    rw [(NativeModel).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil nativeCertificate
      (nativeProfile runtime leaks initial horizon scheduler profile)
      (fun history => ¬ NativeClear runtime leaks initial horizon scheduler history) native,
      PMF.map_bind]
  rw [firstLaw, secondLaw] at close
  simpa only [ite_self, expect_zero, add_zero] using close

end Vegas.EventGraphRuntime.RecoveryProjection
