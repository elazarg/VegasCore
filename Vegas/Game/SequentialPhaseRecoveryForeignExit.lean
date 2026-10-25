/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseForeignFailureBound
import Vegas.Game.RecoveryNativeStoppedState
import Vegas.Game.RecoveryNativeForeignReadout

/-! # Physical phase service bounds the actual recovery comparison foreign exits -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "Initial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (oldLeaks)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) Initial horizon
  (oldScheduler)
local notation "NP" => onePacketProtocol setup (oldLeaks) bounds horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup (oldLeaks))
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application setup (oldLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local instance foreignComparisonHistory : Fintype ((RMenu).protocol
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).History :=
  sourceHistoryFintype setup leaks bounds horizon scheduler

local instance foreignComparisonInformation (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds
      ((Vegas.initialLaw setup).map (fun native =>
        (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).InfoState who) :=
  sourceInfoDecidableEq setup leaks bounds horizon scheduler who

local instance foreignComparisonNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance foreignNativeInformation (who : Player) : DecidableEq ((N).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

/-- Every actual clear regular comparison prefix inherits the physical phase
foreign-exit estimate under an arbitrary whole focal recovery policy. -/
theorem recovery_nativeDebtStopped_foreign_mass_le_rank
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (alternative : (R).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (initialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (initialLaw setup)
      horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate : (NP).WellFoundedHistories) (rawCertificate : (RawNative).WellFoundedHistories)
    (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅)
    (current : (recoveryApplication (runtime setup) (oldLeaks)).Control)
    (state : history.state = some current) (event : (graph setup).EventId)
    (turn : current.execution.application.native.publicView.ownTurn? focal = some event)
    (regular : RegularTrace setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n) focal
      (RecoveryOnePacket.nativeClearHistory setup (oldLeaks) bounds horizon (oldScheduler)
        history clear).trace) :
    let strategy := recoveryComparisonStrategy setup leaks bounds horizon scheduler (sequence n)
      (scale n) (positive n).le (le_one n) (weights n)
    ((RecoveryOnePacket.nativeDebtStoppedLaw setup (oldLeaks) bounds horizon (oldScheduler)
      rawCertificate (Profile.update (sig := (R).behavioralSignature) strategy focal alternative)
      focal history).toOuterMeasure {label | ForeignExclusionLabel focal label}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup (oldLeaks)).rank horizon
        (RecoveryProjection.protocolState (runtime setup) (oldLeaks) history.state) := by
  intro strategy
  let updated := Profile.update (sig := (R).behavioralSignature) strategy focal alternative
  let stop := fun state : (application setup (oldLeaks)).ProtocolState => ¬ Clear state ∨
    DecodedState setup (oldLeaks) (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) state
  let exits := {state : (application setup (oldLeaks)).ProtocolState |
    ¬ Clear state ∧ focal ∉ nativeFailureOwners (runtime setup) (oldLeaks) state}
  have eventMass := RecoveryOnePacket.nativeDebtStopped_foreign_mass_eq_public_failure setup
    (oldLeaks) bounds horizon (oldScheduler) rawCertificate updated focal history clear
  have stopEq : (fun final : (RawNative).History =>
      ¬ NativeClear (runtime setup) (oldLeaks) Initial horizon (oldScheduler) final ∨
        DecodedState setup (oldLeaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) final.state) =
      fun final => stop final.state := by
    funext final
    exact propext (or_congr (not_congr (nativeClear_iff_stateInvariant (runtime setup)
      (oldLeaks) Initial horizon (oldScheduler) final)) Iff.rfl)
  erw [stopEq] at eventMass
  have stoppedState := RecoveryOnePacket.native_run_until_map_state_eq_finite setup (oldLeaks)
    bounds horizon (oldScheduler) rawCertificate certificate updated stop history clear
  have stoppedMass := congrArg (fun law : PMF (application setup (oldLeaks)).ProtocolState =>
    (law.toOuterMeasure exits).toReal) stoppedState
  simp only [PMF.toOuterMeasure_map_apply] at stoppedMass
  let projected := RecoveryOnePacket.nativeClearHistory setup (oldLeaks) bounds horizon
    (oldScheduler) history clear
  let nativeCurrent := RecoveryProjection.control (runtime setup) (oldLeaks) current
  have projectedState : projected.state = some nativeCurrent :=
    (RecoveryOnePacket.nativeClearHistory_state setup (oldLeaks) bounds horizon (oldScheduler)
      history clear).trans (congrArg (RecoveryProjection.protocolState (runtime setup) (oldLeaks))
        state)
  let trace : (NP).Trace (some nativeCurrent) := projectedState ▸ projected.trace
  have rebuilt : (⟨some nativeCurrent, trace⟩ : (NP).History) = projected := by
    dsimp only [trace]
    rcases projected with ⟨chosen, prior⟩
    cases projectedState
    rfl
  have regularTransport {first second : (NP).State} (same : first = second)
      (trace : (NP).Trace first)
      (holds : RegularTrace setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n)
        focal trace) :
      RegularTrace setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n) focal
        (same ▸ trace) := by
    cases same
    exact holds
  have nativeRegular := regularTransport projectedState projected.trace regular
  have nativeState : RecoveryProjection.protocolState (runtime setup) (oldLeaks) history.state =
      some nativeCurrent := congrArg (RecoveryProjection.protocolState (runtime setup) (oldLeaks))
    state
  have valid := nativeHistory_record (runtime setup) (oldLeaks) Initial
    (RecoveryOnePacket.initialLaw_initialized setup) horizon (oldScheduler)
    ((RMenu).toRawTrace Initial horizon (oldScheduler) history.trace) clear nativeCurrent
    nativeState
  let alternativeNative : (N).BehavioralPolicy focal := fun input =>
    (alternative (liftInformation (runtime setup) (oldLeaks) input)).map
      (RecoveryOnePacket.sourceNativeChoiceEquiv setup (oldLeaks) bounds horizon (oldScheduler)
        focal input)
  have rate := nativeComparison_foreign_exit_mass_le_rank setup leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n focal alternativeNative
    opportunity inclusion timely certificate (fun _ => False) nativeCurrent trace event turn valid
    nativeRegular
  simp only [or_false] at rate
  rw [rebuilt] at rate
  have profileLaw := RecoveryOnePacket.nativeComparison_stopped_update_eq setup (oldLeaks) bounds
    horizon (oldScheduler) sequence scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n
    (recoveryComparisonFallback setup leaks bounds horizon scheduler) strategy rfl certificate focal
    alternativeNative (fun final => DecodedState setup (oldLeaks) (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) final.state) projected
  have updateLaw := RecoveryOnePacket.sourceNativeProfile_update setup (oldLeaks) bounds horizon
    (oldScheduler) strategy focal alternative
  erw [← updateLaw] at profileLaw
  change _ = (N).runBehavioralUntil certificate
    (RecoveryOnePacket.sourceNativeProfile setup (oldLeaks) bounds horizon (oldScheduler) updated)
    (fun final => stop final.state) projected at profileLaw
  change (((N).runBehavioralUntil certificate
    (Profile.update (sig := (N).behavioralSignature)
      (RecoveryOnePacket.nativeComparisonStrategy setup (oldLeaks) bounds horizon (oldScheduler)
        sequence scale positive le_one
        (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n)
      focal alternativeNative) (fun final => stop final.state) projected).toOuterMeasure _).toReal ≤
      _ at rate
  erw [profileLaw] at rate
  rw [← nativeState] at rate
  exact (eventMass.trans stoppedMass).trans_le rate

end Vegas.SequentialPhase
