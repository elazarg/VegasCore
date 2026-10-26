/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComparisonRetention
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryHonestRecall
import Vegas.Game.RecoveryNativeComparison

/-! # The common comparison strategy retains honest boundary continuations -/

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
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon (NativeScheduler)

/-- Actual recovery service makes every reached honest input nonlate and forced,
so the original common weights retain its honest choice at every future step. -/
theorem nativeComparison_dominatesHonestFrom_boundary [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler)
    (certificate : (NP).WellFoundedHistories)
    (rank : Nat) (start : (NP).History) (anchor : (application setup runtime leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup runtime leaks horizon (NativeScheduler) rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    DominatesHonestFrom setup runtime leaks bounds (initialLaw setup) horizon (NativeScheduler)
      (sequence n) (slotRetention (scale n))
      (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
        positive le_one
        weights n) start := by
  exact OnePacketComparison.assembled_dominatesHonestFrom_boundary setup runtime leaks bounds
    horizon
    (NativeScheduler)
    wellFormed covers capacity sequence scale positive le_one
    (fun n => nativeComparisonWeights setup runtime leaks bounds horizon scheduler (weights n))
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights)
    (nativeComparisonSequence_assembled setup runtime leaks bounds horizon scheduler sequence
      scale positive
      le_one weights) n
    (Recovery.Opportunity.clear_counted_native (runtime := runtime) bounds (initialLaw_initialized
      setup)
      (initialLaw_native setup) opportunity)
    (Recovery.ProtectedInclusion.clear_counted_native (runtime := runtime) bounds
      (initialLaw_initialized setup)
      (initialLaw_native setup) inclusion)
    timely
    (Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds
      (initialLaw_initialized setup)
      (initialLaw_native setup) completes)
    certificate rank start anchor state boundary point decoded intended

end Vegas.RecoveryOnePacket
