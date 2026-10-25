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
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)

local instance : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance (who : Player) : DecidableEq ((N).InfoState who) := Classical.decEq _

/-- Physical singleton phase service bounds the probability of a native first
foreign exclusion before focal source debt, for every focal deviation. -/
theorem nativeComparison_foreign_exit_mass_le_rank (wellFormed : setup.WellFormed) (covers :
  bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (initialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (initialLaw setup)
      horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol setup (oldLeaks) bounds horizon (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol setup (oldLeaks) bounds horizon
      (NativeScheduler)).History → Prop)
    (start : (application setup (oldLeaks)).Control)
    (startTrace :
      (onePacketProtocol setup (oldLeaks) bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨start.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n) focal
      startTrace) :
    (((N).runBehavioralUntil certificate
      (Function.update ((nativeComparisonSequence setup leaks bounds horizon scheduler
        sequence scale
        positive le_one weights n).strategy) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application setup (oldLeaks))
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState setup (oldLeaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).toOuterMeasure
      {final | ¬ ReactiveApplication.stateInvariant (app := application setup (oldLeaks))
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          final.state ∧
        focal ∉ nativeFailureOwners (runtime setup) (oldLeaks) final.state}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup (oldLeaks)).rank horizon (some start) := by
  have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler
    sequence scale positive le_one weights
  exact OnePacketComparison.assembled_foreign_exit_mass_le_rank setup (oldLeaks) bounds horizon
    (NativeScheduler) wellFormed covers capacity sequence scale positive le_one _ _ assembled n
    focal focalPolicy
    (fun control prior clear => PhaseService.Opportunity.clear_native_counted setup leaks bounds
      horizon scheduler delay opportunity prior clear)
    (fun control prior clear => PhaseService.ProtectedInclusion.clear_native_counted setup leaks
      bounds horizon scheduler bound inclusion prior clear)
    timely certificate extraStop start startTrace current turn clear regular

end Vegas.SequentialPhase
