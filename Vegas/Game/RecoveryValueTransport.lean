/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryContinuationLimit

/-! # Actual recovery gains and their common native stopped values -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

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
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication runtime leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup runtime leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks

open Classical in
/-- Expected utility of the existing concrete native debt-stopped law. -/
def nativeDebtStoppedValue {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (certificate : (RawNative).WellFoundedHistories)
    (profile : ∀ who, (R).BehavioralPolicy who) (focal : Player) (history : (RP).History) : ℝ :=
  expect (nativeDebtStoppedLaw setup runtime leaks bounds horizon scheduler certificate profile
    focal
    history)
    (Sum.elim (fun _ : Finset Player => excludedPayoff focal)
      (fun final : (RawNative).History =>
        if DecodedState setup runtime leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure focal setup.program) final.state then excludedPayoff focal
        else exclusionBase setup runtime parameter utility excludedPayoff leaks final.state focal))

end Vegas.RecoveryOnePacket
