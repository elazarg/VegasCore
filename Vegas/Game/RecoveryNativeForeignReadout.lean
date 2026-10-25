/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryDebtStoppedBelief

/-! # Native classified foreign exits are the actual public-failure event -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

open Classical in
/-- The classified native foreign-exit event is exactly public evidence failure
while the focal owner has no native public failure. -/
theorem nativeClassified_foreign_exit_iff
    (focal : Player) (history : (RawNative).History) :
    ForeignExclusionLabel focal
        (nativeClassifiedReadout (runtime setup) leaks Initial horizon scheduler history) ↔
      ¬ ClearState history.state ∧
        focal ∉ nativeFailureOwners (runtime setup) leaks history.state := by
  rw [← nativeClear_iff_stateInvariant (runtime setup) leaks Initial horizon scheduler
    history]
  by_cases clear : NativeClear (runtime setup) leaks Initial horizon scheduler history <;>
    simp only [nativeClassifiedReadout, clear, ite_true, ite_false, ForeignExclusionLabel,
      not_true_eq_false, not_false_eq_true, false_and, true_and]

open Classical in
/-- The existing concrete native debt-stopped foreign mass is the actual public
failure event used by native comparison estimates. -/
theorem nativeDebtStopped_foreign_mass_eq_public_failure
    (rawCertificate : (RawNative).WellFoundedHistories)
    (profile : ∀ who, (R).BehavioralPolicy who) (focal : Player) (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    ((nativeDebtStoppedLaw setup leaks bounds horizon scheduler rawCertificate profile focal
      history).toOuterMeasure {label | ForeignExclusionLabel focal label}).toReal =
      ((((application setup leaks).information ((Initial).map RecoveryState.native) horizon
        (NativeScheduler)).runBehavioralUntil rawCertificate
        (nativeProfile (runtime setup) leaks Initial horizon scheduler
          (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)))
        (fun final => ¬ NativeClear (runtime setup) leaks Initial horizon scheduler final ∨
          DecodedState setup leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure focal setup.program) final.state)
        (nativeHistory (runtime setup) leaks Initial horizon scheduler
          ((RMenu).toRawHistory Initial horizon scheduler history) clear)).toOuterMeasure
        {final | ¬ ClearState final.state ∧
          focal ∉ nativeFailureOwners (runtime setup) leaks final.state}).toReal := by
  unfold nativeDebtStoppedLaw
  rw [dite_eq_left clear, PMF.toOuterMeasure_map_apply]
  congr 2
  ext final
  exact nativeClassified_foreign_exit_iff setup leaks horizon scheduler focal final

end Vegas.RecoveryOnePacket
