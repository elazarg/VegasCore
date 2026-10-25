/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComparisonRetention
import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.SequentialPhaseNativeComparison

/-! # Honest retention in actual native comparisons under physical phase service -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : PhaseService.Opportunity (runtime setup) leaks (phaseInitialLaw setup) horizon
    scheduler delay)
  (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (phaseInitialLaw setup) horizon
    scheduler bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : PhaseService.CompletesPlay (runtime setup) leaks (phaseInitialLaw setup) horizon
    scheduler)

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup)
    (RecoveryLeaks)
  (recoveryScheduler setup leaks scheduler)
local notation "N" => onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
  (nativeScheduler)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)
local notation "NativeModel" => onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
  horizon (nativeScheduler)
local notation "NativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

include opportunity inclusion timely completes in
theorem nativeComparison_dominatesHonestFrom_boundary
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (n : ℕ)
    (certificate : (NP).WellFoundedHistories)
    (rank : Nat) (start : (NP).History) (anchor : (application setup (RecoveryLeaks)).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup (RecoveryLeaks) horizon (nativeScheduler) rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    DominatesHonestFrom setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
        (nativeScheduler)
      (sequence n) (slotRetention (scale n))
      ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n).strategy) start  := by
  have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler
    sequence scale positive le_one weights
  exact OnePacketComparison.assembled_dominatesHonestFrom_boundary setup (RecoveryLeaks) bounds
      horizon
    (nativeScheduler) wellFormed covers capacity sequence scale positive le_one _ _ assembled n
    (fun control trace clear => PhaseService.Opportunity.clear_native_counted setup leaks bounds
      horizon scheduler delay opportunity trace clear)
    (fun control trace clear => PhaseService.ProtectedInclusion.clear_native_counted setup leaks
      bounds horizon scheduler bound inclusion trace clear)
    timely
    (fun control trace clear terminal => PhaseService.CompletesPlay.clear_native_counted setup
      leaks bounds horizon scheduler completes trace clear terminal)
    certificate rank start anchor state boundary point decoded intended

include opportunity inclusion timely completes in
theorem nativeComparison_dominatesHonestFrom_initialized
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (n : ℕ)
    (certificate : (NP).WellFoundedHistories) :
    DominatesHonestFrom setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
        (nativeScheduler)
      (sequence n) (slotRetention (scale n))
      ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n).strategy) (NP).initHistory  := by
  have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler
    sequence scale positive le_one weights
  exact OnePacketComparison.assembled_dominatesHonestFrom_initialized setup (RecoveryLeaks) bounds
    horizon
    (nativeScheduler) wellFormed covers capacity sequence scale positive le_one _ _ assembled n
    (fun control trace clear => PhaseService.Opportunity.clear_native_counted setup leaks bounds
      horizon scheduler delay opportunity trace clear)
    (fun control trace clear => PhaseService.ProtectedInclusion.clear_native_counted setup leaks
      bounds horizon scheduler bound inclusion trace clear)
    timely
    (fun control trace clear terminal => PhaseService.CompletesPlay.clear_native_counted setup
      leaks bounds horizon scheduler completes trace clear terminal)
    certificate

end Vegas.SequentialPhase
