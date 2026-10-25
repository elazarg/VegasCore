/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonMixture
import Vegas.Game.SequentialPhaseComparisonRepresentation

/-! # Global recovery comparison assessments for actual phase weights

The comparison is fully mixed and Bayes consistent under its own global laws.
It agrees with actual phase component mixtures at every clear played input,
without imposing any recovery optimality or post-exclusion policy equality.
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

local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

def recoveryComparisonFallback : ∀ who, (R).Policy who := fun _ _ => Classical.arbitrary _

/-- A global assembled comparison profile using the transported pool weights. -/
def recoveryComparisonStrategy (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) :
    ∀ who, (R).BehavioralPolicy who :=
  (R).agentBehavior (R).playedInformation
    (recoveryComparisonFallback setup leaks bounds horizon scheduler) fun agent =>
      (recoveryComparisonWeights setup leaks bounds horizon scheduler weights
        (RecoveryOnePacket.pool setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
          agent)).bind
        (RecoveryOnePacket.component setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
          assessment scale nonnegative le_one agent)

theorem recoveryComparisonStrategy_fullSupport
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) :
    ∀ who (site : (R).InformationSite who) (choice : (R).Choice who site.1),
      choice ∈ (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
        positive.le le_one weights who site.1).support := by
  intro who site choice
  rw [recoveryComparisonStrategy, (R).agentBehavior_at (R).playedInformation
    (recoveryComparisonFallback setup leaks bounds horizon scheduler) _ ((R).agentAt site)]
  obtain ⟨part, member⟩ := (recoveryComparisonWeights setup leaks bounds horizon scheduler weights
    (RecoveryOnePacket.pool setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
      ((R).agentAt site))).support_nonempty
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨part, member,
    RecoveryOnePacket.component_fullSupport setup (oldLeaks) bounds (oldInitial) horizon
      (oldScheduler) assessment positive le_one ((R).agentAt site) part choice⟩

/-- Its law at a represented clear site is exactly the original phase mixture. -/
theorem recoveryComparisonStrategy_at_clear
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights agent.1
          (projectedAgent setup leaks bounds horizon scheduler agent clear).2.1 =
      ((weights (pool setup leaks bounds horizon scheduler agent)).bind
        (component setup leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent)).map (choiceEquiv setup leaks bounds horizon scheduler agent clear) := by
  exact ((R).agentBehavior_at (R).playedInformation
    (recoveryComparisonFallback setup leaks bounds horizon scheduler) _
    (projectedAgent setup leaks bounds horizon scheduler agent clear)).trans
      (recoveryComparisonMixture_choice setup leaks bounds horizon scheduler assessment scale
        nonnegative le_one weights agent clear).symm

/-- Canonical Bayes assessments for the actual globally assembled comparison laws. -/
def recoveryComparisonSequence (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    (R).BehavioralAssessment :=
  (R).bayesAssessment
    (recoveryComparisonStrategy setup leaks bounds horizon scheduler (source n) (scale n)
      (positive n).le (le_one n) (weights n))
    (recoveryComparisonStrategy_fullSupport setup leaks bounds horizon scheduler (source n)
      (positive n) (le_one n) (weights n))
    ((oldMenu).decisionRecall (oldInitial) horizon (oldScheduler)).decisionInformationAntichain

theorem recoveryComparisonSequence_assembled
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    (recoveryComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
      weights n).strategy =
      recoveryComparisonStrategy setup leaks bounds horizon scheduler (source n) (scale n)
        (positive n).le (le_one n) (weights n) := rfl

theorem recoveryComparisonSequence_fullyMixed
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    (recoveryComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
      weights n).IsFullyMixed :=
  recoveryComparisonStrategy_fullSupport setup leaks bounds horizon scheduler (source n)
    (positive n) (le_one n) (weights n)

theorem recoveryComparisonSequence_bayes
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ) :
    BehavioralAssessment.IsBayesConsistent (R)
      (recoveryComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights n)
      ((oldMenu).decisionRecall (oldInitial) horizon (oldScheduler)).decisionInformationAntichain :=
  (R).bayesAssessment_isBayesConsistent _ _ _

end Vegas.SequentialPhase
