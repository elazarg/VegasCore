/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryValueTransport
import Vegas.Game.RecoveryDebtStoppedReadout

/-! # Actual belief averages of recovery and native debt-stopped values -/

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
/-- Averaged actual bounded recovery stopped utility is the existing native
stopped value, and its foreign-exit mass is bounded by the same native law.
Only initialized clear starting histories are used; no recovery service is assumed. -/
theorem debt_stopped_belief_eq_native_and_foreign_mass_le [Finite (RP).History]
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (recoveryCertificate : ((recoveryApplication runtime leaks).protocol Initial horizon
      scheduler).WellFoundedHistories)
    (menuCertificate : (RP).WellFoundedHistories)
    (profile : ∀ who, (R).BehavioralPolicy who) (focal : Player)
    (belief : PMF (RP).History)
    (controlled : ∀ history ∈ belief.support,
      ∃ current : (recoveryApplication runtime leaks).Control,
        history.state = some current ∧ current.execution.application.excluded = ∅) :
    let stop := fun history : (RP).History =>
      ¬ ReactiveApplication.stateInvariant (app := RApp)
        (fun state => state.excluded = ∅) history.state ∨
      RecoveryDecodedState (runtime := runtime) (leaks := leaks) (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state
    let kernel := (R).runBehavioralUntil menuCertificate profile stop
    let read := fun history : (RP).History =>
      if RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := leaks)
        history.state ∨
          RecoveryDecodedState (runtime := runtime) (leaks := leaks) (failureProfile setup.program)
            (ProtocolState.OwesFailure focal setup.program) history.state then
        excludedPayoff focal else
        recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff history.state
          focal
    let foreign := {history : (RP).History |
      (RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := leaks)
        history.state ∨
        RecoveryDecodedState (runtime := runtime) (leaks := leaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state) ∧
      ¬ RecoveryExcluded (runtime := runtime) (setup := setup) (leaks := leaks) focal
        history.state ∧
      ¬ RecoveryDecodedState (runtime := runtime) (leaks := leaks) (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state}
    let nativeKernel := nativeDebtStoppedLaw setup runtime leaks bounds horizon scheduler
      rawCertificate
      profile focal
    expect (belief.bind kernel) read = expect belief (fun history =>
      nativeDebtStoppedValue setup runtime leaks bounds horizon scheduler parameter utility
        excludedPayoff
        rawCertificate profile focal history) ∧
      ((belief.bind kernel).toOuterMeasure foreign).toReal ≤
        ((belief.bind nativeKernel).toOuterMeasure
          {label | ForeignExclusionLabel focal label}).toReal := by
  intro stop kernel read foreign nativeKernel
  have stopEq : stop = fun history =>
      RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := leaks) history.state ∨
        RecoveryDecodedState (runtime := runtime) (leaks := leaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state := by
    funext history
    dsimp only [stop]
    cases history.state <;>
      simp only [ReactiveApplication.stateInvariant, RecoveryPublicExclusion, not_true_eq_false]
  have pointwise (history) (supported : history ∈ belief.support) :
      expect (kernel history) read =
        nativeDebtStoppedValue setup runtime leaks bounds horizon scheduler parameter utility
          excludedPayoff
          rawCertificate profile focal history ∧
      ((kernel history).toOuterMeasure foreign).toReal ≤
        ((nativeKernel history).toOuterMeasure
          {label | ForeignExclusionLabel focal label}).toReal := by
    obtain ⟨current, state, empty⟩ := controlled history supported
    have clear : ∀ next, history.state = some next → next.execution.application.excluded = ∅ := by
      intro next found
      cases Option.some.inj (state.symm.trans found)
      exact empty
    have readout := recovery_debt_stopped_expect_eq_native (runtime := runtime) parameter utility
      excludedPayoff
      (failureProfile setup.program) Initial (initialLaw_initialized setup) horizon scheduler
      (RMenu) rawCertificate recoveryCertificate menuCertificate profile focal history current
      state empty
    have mass := recovery_debt_foreign_exit_mass_le_native (runtime := runtime) (failureProfile
      setup.program) Initial
      (initialLaw_initialized setup) horizon scheduler (RMenu) rawCertificate recoveryCertificate
      menuCertificate profile focal history current state empty
    dsimp only [kernel]
    rw [stopEq]
    constructor
    · unfold nativeDebtStoppedValue nativeDebtStoppedLaw
      rw [dite_eq_left clear]
      convert readout using 1
    · dsimp only [nativeKernel, nativeDebtStoppedLaw]
      rw [dite_eq_left clear]
      convert mass using 1
  constructor
  · rw [expect_bind_of_finite]
    exact expect_congr_on_support (fun history supported => (pointwise history supported).1)
  · rw [toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind]
    exact expect_mono (fun history supported => (pointwise history supported).2)
      (payoffIntegrable_toReal_toOuterMeasure belief kernel foreign)
      (payoffIntegrable_toReal_toOuterMeasure belief nativeKernel _)

end Vegas.RecoveryOnePacket
