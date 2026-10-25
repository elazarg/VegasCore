/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseRecoveryComparison

/-! # Native assembled comparisons derived from actual phase weights

The existing recovery-to-native comparison factory uses the same canonical
initialized source prior. All native nature instances are derived from actual
phase nature; no service or incentive property is transferred.
-/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "sourceInitial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (Vegas.initialLaw setup)
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (nativeScheduler)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

local instance sourceHistoryFintype :
    Fintype ((Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds).protocol (sourceInitial)
      horizon (oldScheduler)).History := by
  have nature : (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature (sourceInitial)
      (oldScheduler) := recoveryNature setup leaks scheduler
  exact @ReactiveApplication.ResponseMenu.historyFintype Player _ _
    (Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds) (sourceInitial) horizon
      (oldScheduler) inferInstance nature

local instance sourceInfoDecidableEq (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds (sourceInitial) horizon
      (oldScheduler)).InfoState who) := Classical.decEq _

local instance nativeNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (nativeScheduler) := by
  have nature : (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature (sourceInitial)
      (oldScheduler) := recoveryNature setup leaks scheduler
  have := nature
  exact RecoveryOnePacket.sourceNativeFiniteNature setup (oldLeaks) (oldScheduler)

local instance nativeInfoDecidableEq (who : Player) : DecidableEq ((N).InfoState who) :=
  Classical.decEq _

/-- The native comparison sequence reuses the existing globally assembled
recovery-to-native factory, with no transferred optimality claim. -/
def nativeComparisonSequence (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    (N).BehavioralAssessment := by
  let := sourceHistoryFintype setup leaks bounds horizon scheduler
  let := sourceInfoDecidableEq setup leaks bounds horizon scheduler
  let := nativeNature setup leaks scheduler
  let := nativeInfoDecidableEq setup leaks bounds horizon scheduler
  exact RecoveryOnePacket.nativeComparisonSequence setup (oldLeaks) bounds horizon (oldScheduler)
    source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n

theorem nativeComparisonSequence_assembled
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) :
    letI := sourceHistoryFintype setup leaks bounds horizon scheduler
    letI := sourceInfoDecidableEq setup leaks bounds horizon scheduler
    letI := nativeNature setup leaks scheduler
    letI := nativeInfoDecidableEq setup leaks bounds horizon scheduler
    OnePacketAssembled setup (oldLeaks) bounds horizon (nativeScheduler) source scale
      positive le_one
      (fun n => RecoveryOnePacket.nativeComparisonWeights setup (oldLeaks) bounds horizon
        (oldScheduler) (recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)))
      (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights) := by
  let := sourceHistoryFintype setup leaks bounds horizon scheduler
  let := sourceInfoDecidableEq setup leaks bounds horizon scheduler
  let := nativeNature setup leaks scheduler
  let := nativeInfoDecidableEq setup leaks bounds horizon scheduler
  exact RecoveryOnePacket.nativeComparisonSequence_assembled setup (oldLeaks) bounds horizon
    (oldScheduler) source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n))

theorem nativeComparisonSequence_fullyMixed
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
      weights n).IsFullyMixed := by
  let := sourceHistoryFintype setup leaks bounds horizon scheduler
  let := sourceInfoDecidableEq setup leaks bounds horizon scheduler
  let := nativeNature setup leaks scheduler
  let := nativeInfoDecidableEq setup leaks bounds horizon scheduler
  exact RecoveryOnePacket.nativeComparisonSequence_fullyMixed setup (oldLeaks) bounds horizon
    (oldScheduler) source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n

theorem nativeComparisonSequence_bayes
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    BehavioralAssessment.IsBayesConsistent (N)
      (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights n)
      ((bounds.onePacketMenu (runtime setup) (oldLeaks)).decisionInformationAntichain
        (Vegas.initialLaw setup) horizon (nativeScheduler)) := by
  let := sourceHistoryFintype setup leaks bounds horizon scheduler
  let := sourceInfoDecidableEq setup leaks bounds horizon scheduler
  let := nativeNature setup leaks scheduler
  let := nativeInfoDecidableEq setup leaks bounds horizon scheduler
  exact RecoveryOnePacket.nativeComparisonSequence_bayes setup (oldLeaks) bounds horizon
    (oldScheduler) source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n

end Vegas.SequentialPhase
