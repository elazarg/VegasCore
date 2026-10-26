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
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu runtime (RecoveryLeaks)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) RecoveryPrior horizon
  (RecoveryScheduler)
local notation "NP" => onePacketProtocol (runtime := runtime) setup (RecoveryLeaks) bounds horizon
  (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application (runtime := runtime) setup
  (RecoveryLeaks))
  (PMF.map RecoveryState.native (RecoveryPrior)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application (runtime :=
  runtime) setup
    (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- Every actual clear regular comparison prefix inherits the physical phase
foreign-exit estimate under an arbitrary whole focal recovery policy. -/
theorem recovery_nativeDebtStopped_foreign_mass_le_rank
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (alternative : (R).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity runtime leaks (phaseInitialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion runtime leaks (phaseInitialLaw setup)
      horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (certificate : (NP).WellFoundedHistories) (rawCertificate : (RawNative).WellFoundedHistories)
    (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅)
    (current : (recoveryApplication runtime (RecoveryLeaks)).Control)
    (state : history.state = some current) (event : (graph setup).EventId)
    (turn : current.execution.application.native.publicView.ownTurn? focal = some event)
    (regular : RegularTrace (runtime := runtime) setup (RecoveryLeaks) bounds horizon
      (NativeScheduler) (sequence n)
        focal
      (RecoveryOnePacket.nativeClearHistory (runtime := runtime) setup (RecoveryLeaks) bounds
        horizon (RecoveryScheduler)
        history clear).trace) :
    let strategy := recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler
      (sequence n)
      (scale n) (positive n).le (le_one n) (weights n)
    ((RecoveryOnePacket.nativeDebtStoppedLaw (runtime := runtime) setup (RecoveryLeaks) bounds
      horizon
        (RecoveryScheduler)
      rawCertificate (Profile.update (sig := (R).behavioralSignature) strategy focal alternative)
      focal history).toOuterMeasure {label | ForeignExclusionLabel focal label}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application (runtime := runtime) setup (RecoveryLeaks)).rank
        horizon
        (RecoveryProjection.protocolState runtime (RecoveryLeaks) history.state) := by
  intro strategy
  let updated := Profile.update (sig := (R).behavioralSignature) strategy focal alternative
  let stop := fun state : (application (runtime := runtime) setup (RecoveryLeaks)).ProtocolState
    => ¬ Clear state ∨
    DecodedState (runtime := runtime) setup (RecoveryLeaks) (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) state
  let exits := {state : (application (runtime := runtime) setup (RecoveryLeaks)).ProtocolState |
    ¬ Clear state ∧ focal ∉ nativeFailureOwners runtime (RecoveryLeaks) state}
  have eventMass := RecoveryOnePacket.nativeDebtStopped_foreign_mass_eq_public_failure (runtime :=
    runtime) setup
    (RecoveryLeaks) bounds horizon (RecoveryScheduler) rawCertificate updated focal history clear
  have stopEq : (fun final : (RawNative).History =>
      ¬ NativeClear runtime (RecoveryLeaks) RecoveryPrior horizon (RecoveryScheduler) final
          ∨
        DecodedState (runtime := runtime) setup (RecoveryLeaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) final.state) =
      fun final => stop final.state := by
    funext final
    exact propext (or_congr (not_congr (nativeClear_iff_stateInvariant runtime
      (RecoveryLeaks) RecoveryPrior horizon (RecoveryScheduler) final)) Iff.rfl)
  erw [stopEq] at eventMass
  have stoppedState := RecoveryOnePacket.native_run_until_map_state_eq_finite (runtime := runtime)
    setup (RecoveryLeaks)
    bounds horizon (RecoveryScheduler) rawCertificate certificate updated stop history clear
  have stoppedMass := congrArg (fun law : PMF (application (runtime := runtime) setup
    (RecoveryLeaks)).ProtocolState =>
    (law.toOuterMeasure exits).toReal) stoppedState
  simp only [PMF.toOuterMeasure_map_apply] at stoppedMass
  let projected := RecoveryOnePacket.nativeClearHistory (runtime := runtime) setup (RecoveryLeaks)
    bounds horizon
    (RecoveryScheduler) history clear
  let nativeCurrent := RecoveryProjection.control runtime (RecoveryLeaks) current
  have projectedState : projected.state = some nativeCurrent :=
    (RecoveryOnePacket.nativeClearHistory_state (runtime := runtime) setup (RecoveryLeaks) bounds
      horizon
        (RecoveryScheduler)
      history clear).trans (congrArg (RecoveryProjection.protocolState runtime
          (RecoveryLeaks))
        state)
  let trace : (NP).Trace (some nativeCurrent) := projectedState ▸ projected.trace
  have rebuilt : (⟨some nativeCurrent, trace⟩ : (NP).History) = projected := by
    dsimp only [trace]
    rcases projected with ⟨chosen, prior⟩
    cases projectedState
    rfl
  have regularTransport {first second : (NP).State} (same : first = second)
      (trace : (NP).Trace first)
      (holds : RegularTrace (runtime := runtime) setup (RecoveryLeaks) bounds horizon
        (NativeScheduler) (sequence n)
        focal trace) :
      RegularTrace (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler)
        (sequence n) focal
        (same ▸ trace) := by
    cases same
    exact holds
  have nativeRegular := regularTransport projectedState projected.trace regular
  have nativeState : RecoveryProjection.protocolState runtime (RecoveryLeaks) history.state
      =
      some nativeCurrent := congrArg (RecoveryProjection.protocolState runtime
          (RecoveryLeaks))
    state
  have valid := nativeHistory_record runtime (RecoveryLeaks) RecoveryPrior
    (RecoveryOnePacket.initialLaw_initialized setup) horizon (RecoveryScheduler)
    ((RMenu).toRawTrace RecoveryPrior horizon (RecoveryScheduler) history.trace) clear nativeCurrent
    nativeState
  let alternativeNative : (N).BehavioralPolicy focal := fun input =>
    (alternative (liftInformation runtime (RecoveryLeaks) input)).map
      (RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup (RecoveryLeaks) bounds
        horizon
          (RecoveryScheduler)
        focal input)
  have rate := nativeComparison_foreign_exit_mass_le_rank setup runtime leaks bounds horizon
    scheduler
    wellFormed covers capacity sequence scale positive le_one weights n focal alternativeNative
    opportunity inclusion timely certificate (fun _ => False) nativeCurrent trace event turn valid
    nativeRegular
  simp only [or_false] at rate
  rw [rebuilt] at rate
  have profileLaw := RecoveryOnePacket.nativeComparison_stopped_update_eq (runtime := runtime)
    setup (RecoveryLeaks)
      bounds
    horizon (RecoveryScheduler) sequence scale positive le_one
    (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights n)) n
    (recoveryComparisonFallback setup runtime leaks bounds horizon scheduler) strategy rfl
      certificate focal
    alternativeNative (fun final => DecodedState (runtime := runtime) setup (RecoveryLeaks)
      (failureProfile
        setup.program)
      (ProtocolState.OwesFailure focal setup.program) final.state) projected
  have updateLaw := RecoveryOnePacket.sourceNativeProfile_update (runtime := runtime) setup
    (RecoveryLeaks) bounds
      horizon
    (RecoveryScheduler) strategy focal alternative
  erw [← updateLaw] at profileLaw
  change _ = (N).runBehavioralUntil certificate
    (RecoveryOnePacket.sourceNativeProfile (runtime := runtime) setup (RecoveryLeaks) bounds
      horizon (RecoveryScheduler)
        updated)
    (fun final => stop final.state) projected at profileLaw
  change (((N).runBehavioralUntil certificate
    (Profile.update (sig := (N).behavioralSignature)
      (RecoveryOnePacket.nativeComparisonStrategy (runtime := runtime) setup (RecoveryLeaks)
        bounds horizon
          (RecoveryScheduler)
        sequence scale positive le_one
        (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights
          n)) n)
      focal alternativeNative) (fun final => stop final.state) projected).toOuterMeasure _).toReal ≤
      _ at rate
  erw [profileLaw] at rate
  rw [← nativeState] at rate
  exact (eventMass.trans stoppedMass).trans_le rate

end Vegas.SequentialPhase
