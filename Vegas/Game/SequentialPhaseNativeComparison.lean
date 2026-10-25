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
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup leaks scheduler
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup)
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "N" => onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
  (nativeScheduler)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- The native comparison sequence reuses the existing globally assembled
recovery-to-native factory, with no transferred optimality claim. -/
def nativeComparisonSequence (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    (N).BehavioralAssessment :=
  RecoveryOnePacket.nativeComparisonSequence setup (RecoveryLeaks) bounds horizon
      (RecoveryScheduler)
    source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n

theorem nativeComparisonSequence_assembled
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) :
    OnePacketAssembled setup (RecoveryLeaks) bounds horizon (nativeScheduler) source scale
      positive le_one
      (fun n => RecoveryOnePacket.nativeComparisonWeights setup (RecoveryLeaks) bounds horizon
        (RecoveryScheduler) (recoveryComparisonWeights setup leaks bounds horizon scheduler (weights
            n)))
      (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights) :=
  RecoveryOnePacket.nativeComparisonSequence_assembled setup (RecoveryLeaks) bounds horizon
    (RecoveryScheduler) source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n))

theorem nativeComparisonSequence_fullyMixed
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
      weights n).IsFullyMixed :=
  RecoveryOnePacket.nativeComparisonSequence_fullyMixed setup (RecoveryLeaks) bounds horizon
    (RecoveryScheduler) source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n

theorem nativeComparisonSequence_bayes
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    BehavioralAssessment.IsBayesConsistent (N)
      (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights n)
      ((bounds.onePacketMenu (runtime setup) (RecoveryLeaks)).decisionInformationAntichain
        (Vegas.initialLaw setup) horizon (nativeScheduler)) :=
  RecoveryOnePacket.nativeComparisonSequence_bayes setup (RecoveryLeaks) bounds horizon
    (RecoveryScheduler) source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n

end Vegas.SequentialPhase
