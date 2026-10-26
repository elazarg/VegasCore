/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeWeights
import GameTheory.Analysis.Protocol.BehavioralBayes

/-! # Globally assembled native comparison profiles

The recovery completion weights determine ordinary native component mixtures.
Their canonical Bayes assessments supply global assembly and full support for
prefix likelihood estimates. No native incentive or completion property is
asserted.
-/

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

/-- The globally assembled native comparison strategy, using the same recovery
weights on represented pools. -/
def nativeComparisonStrategy [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ) :
    ∀ who, (N).BehavioralPolicy who :=
  (N).agentBehavior (N).playedInformation
    (onePacketFallback setup runtime leaks bounds horizon (NativeScheduler)) fun agent =>
      (nativeComparisonWeights setup runtime leaks bounds horizon scheduler (weights n)
        (onePacketPool setup runtime leaks bounds horizon (NativeScheduler) agent)).bind
          (onePacketComponent setup runtime leaks bounds horizon (NativeScheduler) (sequence n)
            (scale n) (positive n).le (le_one n) agent)

/-- Every native comparison decision law has full support. -/
theorem nativeComparisonStrategy_fullSupport [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ) :
    ∀ who (site : (N).InformationSite who) (choice : (N).Choice who site.1),
      choice ∈ (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
        positive le_one weights n who site.1).support := by
  intro who site choice
  rw [nativeComparisonStrategy, (N).agentBehavior_at (N).playedInformation
    (onePacketFallback setup runtime leaks bounds horizon (NativeScheduler)) _ ((N).agentAt site)]
  obtain ⟨part, member⟩ :=
    (nativeComparisonWeights setup runtime leaks bounds horizon scheduler (weights n)
      (onePacketPool setup runtime leaks bounds horizon (NativeScheduler)
        ((N).agentAt site))).support_nonempty
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨part, member,
    onePacketComponent_fullSupport setup runtime leaks bounds horizon (NativeScheduler) (sequence n)
      (positive n) (le_one n) ((N).agentAt site) part choice⟩

/-- Canonical Bayes assessments of the native comparison strategies. -/
def nativeComparisonSequence [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ) :
    (N).BehavioralAssessment :=
  (N).bayesAssessment
    (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights n)
    (nativeComparisonStrategy_fullSupport setup runtime leaks bounds horizon scheduler sequence
      scale
      positive le_one weights n)
    ((bounds.onePacketMenu runtime leaks).decisionInformationAntichain (initialLaw setup)
      horizon (NativeScheduler))

/-- The comparison sequence meets the original global component-assembly
identity, with exactly the deterministically extended recovery weights. -/
theorem nativeComparisonSequence_assembled [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p)) :
    OnePacketAssembled setup runtime leaks bounds horizon (NativeScheduler) sequence scale
      positive le_one
      (fun n => nativeComparisonWeights setup runtime leaks bounds horizon scheduler (weights n))
      (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
        positive le_one
        weights) := by
  intro n
  rfl

/-- The comparison assessments are fully mixed, independently of incentives. -/
theorem nativeComparisonSequence_fullyMixed [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ) :
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights n).IsFullyMixed :=
  nativeComparisonStrategy_fullSupport setup runtime leaks bounds horizon scheduler sequence scale
    positive
    le_one weights n

/-- The comparison assessments obey Bayes' rule for their own assembled laws. -/
theorem nativeComparisonSequence_bayes [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ) :
    BehavioralAssessment.IsBayesConsistent (N)
      (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
        positive le_one
        weights n)
      ((bounds.onePacketMenu runtime leaks).decisionInformationAntichain (initialLaw setup)
        horizon (NativeScheduler)) :=
  (N).bayesAssessment_isBayesConsistent
    (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights n)
    (nativeComparisonStrategy_fullSupport setup runtime leaks bounds horizon scheduler sequence
      scale
      positive le_one weights n)
    ((bounds.onePacketMenu runtime leaks).decisionInformationAntichain (initialLaw setup)
      horizon (NativeScheduler))

end Vegas.RecoveryOnePacket
