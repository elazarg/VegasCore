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
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (nativeScheduler)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

open Classical in
/-- Actual phase weights supply the complete old-to-native comparison fiber
and Bayes belief at each forced debt-free old input. The source prior and
comparison sequences are the constructed ones, rather than additional premises. -/
theorem exists_native_comparison_information
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) :
    letI := sourceHistoryFintype setup leaks bounds horizon scheduler
    letI := sourceInfoDecidableEq setup leaks bounds horizon scheduler
    letI := nativeNature setup leaks scheduler
    letI := nativeInfoDecidableEq setup leaks bounds horizon scheduler
    ∀ n who (site : (R).InformationSite who),
    (¬ RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
      ((R).agentAt site)) →
    (¬ RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
      ((R).agentAt site)) →
    ∃ (nativeSite : (N).InformationSite who)
      (project : (R).InformationHistory who site.1 → (N).InformationHistory who nativeSite.1),
      nativeSite.1 = RecoveryProjection.information (runtime setup) (oldLeaks) site.1 ∧
      ¬ Vegas.FreeAgent setup (oldLeaks) bounds horizon (nativeScheduler) ((N).agentAt nativeSite) ∧
      ¬ Vegas.OwingAgent setup (oldLeaks) bounds horizon (nativeScheduler)
        ((N).agentAt nativeSite) ∧
      (∀ history : (R).InformationHistory who site.1, ∃ clear :
          ∀ current, history.1.state = some current →
            current.execution.application.excluded = ∅,
        (bounds.onePacketMenu (runtime setup) (oldLeaks)).toRawHistory (Vegas.initialLaw setup)
            horizon (nativeScheduler) (project history).1 =
          Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
            ((application setup (oldLeaks)).protocol initial horizon (nativeScheduler)).History)
              (RecoveryOnePacket.initialLaw_native setup))
            (RecoveryProjection.nativeHistory (runtime setup) (oldLeaks) (oldInitial) horizon
              (oldScheduler)
              ((Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds).toRawHistory
                (oldInitial) horizon (oldScheduler) history.1) clear)) ∧
      (∀ history, (project history).1.state =
        RecoveryProjection.protocolState (runtime setup) (oldLeaks) history.1.state) ∧
      ((recoveryComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights n).belief who site).map project =
        (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
          weights n).belief who nativeSite := by
  let := sourceHistoryFintype setup leaks bounds horizon scheduler
  let := sourceInfoDecidableEq setup leaks bounds horizon scheduler
  let := nativeNature setup leaks scheduler
  let := nativeInfoDecidableEq setup leaks bounds horizon scheduler
  intro n who site notFree notOwing
  obtain ⟨nativeSite, project, input, nativeNotFree, nativeNotOwing, raw, states, beliefs⟩ :=
    RecoveryOnePacket.exists_comparisonInformationHistory setup (oldLeaks) bounds horizon
      (oldScheduler) source scale positive le_one
      (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n))
      (recoveryComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights)
      (fun _ => recoveryComparisonFallback setup leaks bounds horizon scheduler)
      (by intro n; rfl)
      (fun n => recoveryComparisonSequence_bayes setup leaks bounds horizon scheduler source scale
        positive le_one weights n)
      n who site notFree notOwing
  exact ⟨nativeSite, project, input, nativeNotFree, nativeNotOwing, raw, states, beliefs⟩

end Vegas.SequentialPhase
