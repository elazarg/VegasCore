/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeHistory
import Interaction.ReactivePriorStopped


/-! # Exact raw and bounded native stopped state laws -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection


variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (MessageBounds.onePacketMenu runtime leaks bounds) (initialLaw setup) horizon
  (NativeScheduler)

/-- The concrete native policy induced by an actual bounded recovery profile
has exactly the same stopped physical state law in its raw and bounded encodings.
Only the actual clear starting history is projected; no recovery service is used. -/
theorem native_run_until_map_state_eq_finite
    (rawCertificate : ((application setup runtime leaks).protocol ((Initial).map
      RecoveryState.native)
      horizon (NativeScheduler)).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    (profile : ∀ who, (R).BehavioralPolicy who)
    (stop : (application setup runtime leaks).ProtocolState → Prop)
    (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    ((((application setup runtime leaks).information ((Initial).map RecoveryState.native) horizon
      (NativeScheduler)).runBehavioralUntil rawCertificate
      (nativeProfile runtime leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)))
      (fun final => stop final.state)
      (nativeHistory runtime leaks Initial horizon scheduler
        ((RMenu).toRawHistory Initial horizon scheduler history) clear)).map History.state) =
      (((N).runBehavioralUntil certificate
        (sourceNativeProfile setup runtime leaks bounds horizon scheduler profile)
        (fun final => stop final.state)
        (nativeClearHistory setup runtime leaks bounds horizon scheduler history clear)).map
        History.state) := by
  let genericInitial := (Initial).map RecoveryState.native
  let genericModel := (NMenu).information genericInitial horizon (NativeScheduler)
  let genericProfile := boundedNativeProfile runtime leaks bounds Initial horizon scheduler
    profile
  let genericStart := (exists_nativeBoundedHistory runtime leaks bounds Initial
    (initialLaw_initialized setup) horizon scheduler history clear).choose
  have rawStart : (NMenu).toRawHistory genericInitial horizon (NativeScheduler) genericStart =
      nativeHistory runtime leaks Initial horizon scheduler
        ((RMenu).toRawHistory Initial horizon scheduler history) clear :=
    (exists_nativeBoundedHistory runtime leaks bounds Initial
      (initialLaw_initialized setup) horizon scheduler history clear).choose_spec
  let genericCertificate : ((NMenu).protocol genericInitial horizon
      (NativeScheduler)).WellFoundedHistories :=
    Eq.mpr (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).protocol initial horizon (NativeScheduler)).WellFoundedHistories)
        (initialLaw_native setup)) certificate
  have rawLaw := (NMenu).runBehavioralUntil_embed genericInitial horizon (NativeScheduler)
    rawCertificate genericCertificate genericProfile (fun final => stop final.state) genericStart
  have profiles :
      (fun who => (NMenu).embedPolicy genericInitial horizon (NativeScheduler) who
        (genericProfile who)) =
      nativeProfile runtime leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)) := by
    funext who
    exact boundedNativeProfile_embed runtime leaks bounds Initial horizon scheduler
      profile who
  rw [profiles, rawStart] at rawLaw
  have rawState :
      ((((application setup runtime leaks).information genericInitial horizon
        (NativeScheduler)).runBehavioralUntil rawCertificate
        (nativeProfile runtime leaks Initial horizon scheduler
          (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)))
        (fun final => stop final.state)
        (nativeHistory runtime leaks Initial horizon scheduler
          ((RMenu).toRawHistory Initial horizon scheduler history) clear)).map History.state) =
      ((genericModel.runBehavioralUntil genericCertificate genericProfile
        (fun final => stop final.state) genericStart).map History.state) := by
    have mapped := congrArg (PMF.map History.state) rawLaw
    rw [PMF.map_comp] at mapped
    exact mapped.symm
  have priorLaw := (NMenu).run_until_map_state_prior_eq (initialLaw_native setup) horizon
    (NativeScheduler) genericCertificate certificate genericProfile stop genericStart
  have profileCast :
      (fun who input => (genericProfile who input).map (Equiv.cast (congrArg
        (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
          ((NMenu).information initial horizon (NativeScheduler)).Choice who input)
            (initialLaw_native setup)))) =
        sourceNativeProfile setup runtime leaks bounds horizon scheduler profile := by
    funext who input
    exact (sourceNativeProfile_eq_cast setup runtime leaks bounds horizon scheduler profile who
      input).symm
  erw [profileCast] at priorLaw
  exact rawState.trans priorLaw

end Vegas.RecoveryOnePacket
