/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.RecoveryComparisonSite

/-! # Native comparison information from actual phase component weights -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (nativeScheduler)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

open Classical in
/-- Actual phase weights supply the complete recovery-to-native comparison fiber
and Bayes belief at each forced debt-free recovery input. The source prior and
comparison sequences are the constructed ones, rather than additional premises. -/
theorem exists_native_comparison_information
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p)) :
    ∀ n who (site : (R).InformationSite who),
    (¬ RecoveryOnePacket.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds
      (RecoveryPrior) horizon
        (RecoveryScheduler)
      ((R).agentAt site)) →
    (¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds
      (RecoveryPrior) horizon
        (RecoveryScheduler)
      ((R).agentAt site)) →
    ∃ (nativeSite : (N).InformationSite who)
      (project : (R).InformationHistory who site.1 → (N).InformationHistory who nativeSite.1),
      nativeSite.1 = RecoveryProjection.information runtime (RecoveryLeaks) site.1 ∧
      ¬ Vegas.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon
        (nativeScheduler) ((N).agentAt
          nativeSite) ∧
      ¬ Vegas.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon (nativeScheduler)
        ((N).agentAt nativeSite) ∧
      (∀ history : (R).InformationHistory who site.1, ∃ clear :
          ∀ current, history.1.state = some current →
            current.execution.application.excluded = ∅,
        (bounds.onePacketMenu runtime (RecoveryLeaks)).toRawHistory (Vegas.initialLaw setup)
            horizon (nativeScheduler) (project history).1 =
          Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
            ((application (runtime := runtime) setup (RecoveryLeaks)).protocol initial horizon
                (nativeScheduler)).History)
              (RecoveryOnePacket.initialLaw_native setup))
            (RecoveryProjection.nativeHistory runtime (RecoveryLeaks) (RecoveryPrior)
                horizon
              (RecoveryScheduler)
              ((Recovery.onePacketMenu runtime (RecoveryLeaks) bounds).toRawHistory
                (RecoveryPrior) horizon (RecoveryScheduler) history.1) clear)) ∧
      (∀ history, (project history).1.state =
        RecoveryProjection.protocolState runtime (RecoveryLeaks) history.1.state) ∧
      ((recoveryComparisonSequence setup runtime leaks bounds horizon scheduler source scale
        positive le_one
        weights n).belief who site).map project =
        (nativeComparisonSequence setup runtime leaks bounds horizon scheduler source scale
          positive le_one
          weights n).belief who nativeSite := by
  intro n who site notFree notOwing
  obtain ⟨nativeSite, project, input, nativeNotFree, nativeNotOwing, raw, states, beliefs⟩ :=
    RecoveryOnePacket.exists_comparisonInformationHistory (runtime := runtime) setup
      (RecoveryLeaks) bounds horizon
      (RecoveryScheduler) source scale positive le_one
      (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights n))
      (recoveryComparisonSequence setup runtime leaks bounds horizon scheduler source scale
        positive le_one
        weights)
      (fun _ => recoveryComparisonFallback setup runtime leaks bounds horizon scheduler)
      (by intro n; rfl)
      (fun n => recoveryComparisonSequence_bayes setup runtime leaks bounds horizon scheduler
        source scale
        positive le_one weights n)
      n who site notFree notOwing
  exact ⟨nativeSite, project, input, nativeNotFree, nativeNotOwing, raw, states, beliefs⟩

end Vegas.SequentialPhase
