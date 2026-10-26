/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForeignFailureBound
import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.SequentialPhaseNativeService

/-! # Rare native foreign exits under physical singleton phase service

The estimate uses the actual native comparison assembled from phase component
weights. Physical service is used only at clear counted counterfactual prefixes.
Every focal policy, the source prior, and the remaining-rank error are retained.
-/

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
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (NativeScheduler)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- Physical singleton phase service bounds the probability of a native first
foreign exclusion before focal source debt, for every focal deviation. -/
theorem nativeComparison_foreign_exit_mass_le_rank (wellFormed : setup.WellFormed) (covers :
  bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity runtime leaks (phaseInitialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion runtime leaks (phaseInitialLaw setup)
      horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol (runtime := runtime) setup (RecoveryLeaks) bounds horizon
          (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol (runtime := runtime) setup (RecoveryLeaks) bounds horizon
      (NativeScheduler)).History → Prop)
    (start : (application (runtime := runtime) setup (RecoveryLeaks)).Control)
    (startTrace :
      (onePacketProtocol (runtime := runtime) setup (RecoveryLeaks) bounds horizon
        (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨start.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace (runtime := runtime) setup (RecoveryLeaks) bounds horizon
      (NativeScheduler) (sequence n)
        focal
      startTrace) :
    (((N).runBehavioralUntil certificate
      (Function.update ((nativeComparisonSequence setup runtime leaks bounds horizon scheduler
        sequence scale
        positive le_one weights n).strategy) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application (runtime :=
        runtime) setup
          (RecoveryLeaks))
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState (runtime := runtime) setup (RecoveryLeaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).toOuterMeasure
      {final | ¬ ReactiveApplication.stateInvariant (app := application (runtime := runtime) setup
        (RecoveryLeaks))
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          final.state ∧
        focal ∉ nativeFailureOwners runtime (RecoveryLeaks) final.state}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application (runtime := runtime) setup (RecoveryLeaks)).rank
        horizon (some start) :=
          by
  have assembled := nativeComparisonSequence_assembled setup runtime leaks bounds horizon scheduler
    sequence scale positive le_one weights
  exact OnePacketComparison.assembled_foreign_exit_mass_le_rank (runtime := runtime) setup
    (RecoveryLeaks) bounds horizon
    (NativeScheduler) wellFormed covers capacity sequence scale positive le_one _ _ assembled n
    focal focalPolicy
    (fun control prior clear => PhaseService.Opportunity.clear_native_counted setup runtime leaks
      bounds
      horizon scheduler delay opportunity prior clear)
    (fun control prior clear => PhaseService.ProtectedInclusion.clear_native_counted setup runtime
      leaks
      bounds horizon scheduler bound inclusion prior clear)
    timely certificate extraStop start startTrace current turn clear regular

end Vegas.SequentialPhase
