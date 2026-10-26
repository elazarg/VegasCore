/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeClearReach
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison

/-! # Same-witness continuation laws before public exclusion -/

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
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks

local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk
    state ∅))

/-- The common comparison and actual projected recovery strategy agree at every
clear native history before termination. -/
theorem nativeComparisonStrategy_eq_projection_at_clear [Fintype ((RMenu).protocol Initial horizon
      scheduler).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (R).Policy who)
    (strategy : ∀ who, (R).BehavioralPolicy who)
    (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler
        agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    {before : (application setup runtime leaks).ProtocolState}
    (prior : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).Trace before)
    (valid : ∀ current, before = some current →
      ExclusionEvidence 0 ∅ (RecoveryState.mk current.execution.application ∅))
    (running : ¬ ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).terminal before)
    (who : Player) :
    nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
        weights n who ((N).infoOf who prior) =
      sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy who ((N).infoOf who
        prior) := by
  by_cases active : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).active
      before who
  · obtain ⟨site, seen⟩ := (N).exists_informationSite_of_active who ⟨before, prior⟩ running active
    have recoveryDecision := recoveryDecision_of_nativeClearTrace setup runtime leaks bounds horizon
      scheduler prior valid who active running
    have represented : (R).IsDecisionInfo who (liftInformation runtime leaks site.1) :=
      Eq.mpr (congrArg (fun input => (R).IsDecisionInfo who
        (liftInformation runtime leaks input)) seen) recoveryDecision
    have localLaw : nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence
        scale positive le_one weights n who site.1 =
        sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy who site.1 := by
      apply pmf_map_injective Subtype.val_injective
      rw [sourceNativeProfile_map_val]
      exact nativeComparisonStrategy_at_clear setup runtime leaks bounds horizon scheduler
        sequence scale
        positive le_one weights n fallback strategy assembled site represented
    exact Eq.mp (congrArg (fun input => nativeComparisonStrategy setup runtime leaks bounds horizon
      scheduler sequence scale positive le_one weights n who input =
        sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy who input) seen)
          localLaw
  · exact (N).behavioral_eq_of_not_active _ _ prior active

/-- Against the same arbitrary focal continuation policy, the actual projected
recovery opponents and their same-weight comparison opponents have exactly the
same full history law stopped at public exclusion or any additional condition. -/
theorem nativeComparison_stopped_update_eq [Fintype ((RMenu).protocol Initial horizon
      scheduler).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (R).Policy who)
    (strategy : ∀ who, (R).BehavioralPolicy who)
    (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler
        agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (certificate : ((NMenu).protocol (initialLaw setup) horizon
      (NativeScheduler)).WellFoundedHistories)
    (focal : Player) (alternative : (N).BehavioralPolicy focal)
    (extraStop : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).History → Prop)
    (start : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).History) :
    (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature)
          (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
            positive
            le_one weights n) focal alternative)
        (fun history => ¬ Clear history.state ∨ extraStop history) start =
      (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature)
          (sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy) focal
            alternative)
        (fun history => ¬ Clear history.state ∨ extraStop history) start := by
  let firstProfile := Profile.update (sig := (N).behavioralSignature)
    (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights n) focal alternative
  let secondProfile := Profile.update (sig := (N).behavioralSignature)
    (sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy) focal alternative
  let stopped := fun history : ((NMenu).protocol (initialLaw setup) horizon
      (NativeScheduler)).History => ¬ Clear history.state ∨ extraStop history
  have compared := (N).runBehavioralUntil_map_eq_of_paired_steps (N) certificate certificate
    firstProfile secondProfile stopped stopped id id (fun first second => first = second)
    (by intro first second equal; subst second; rfl)
    (by intro first second equal _halt; subst second; rfl)
    (by
      intro first second equal going running
      subst second
      have clear : Clear first.state := not_not.mp (fun failure => going (Or.inl failure))
      have valid : ∀ current, first.state = some current →
          ExclusionEvidence 0 ∅ (RecoveryState.mk current.execution.application ∅) := by
        intro current state
        rw [state] at clear
        exact clear
      have agree : ∀ who, firstProfile who ((N).infoOf who first.trace) =
          secondProfile who ((N).infoOf who first.trace) := by
        intro who
        dsimp only [firstProfile, secondProfile]
        by_cases same : who = focal
        · subst who
          rw [Profile.update_same, Profile.update_same]
        · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
          exact nativeComparisonStrategy_eq_projection_at_clear setup runtime leaks bounds horizon
            scheduler
            sequence scale positive le_one weights n fallback strategy assembled first.trace valid
              running who
      have oneStep : (N).runBehavioralFrom firstProfile 1 first =
          (N).runBehavioralFrom secondProfile 1 first := by
        rw [(N).runBehavioralFrom_succ_of_not_terminal firstProfile 0 running,
          (N).runBehavioralFrom_succ_of_not_terminal secondProfile 0 running,
          (N).behavioralJoint_congr first.trace running agree]
        rfl
      let law := (N).runBehavioralFrom firstProfile 1 first
      refine ⟨law.map (fun history => (history, history)), ?_, ?_, ?_⟩
      · rw [PMF.map_comp]
        exact PMF.map_id law
      · rw [PMF.map_comp]
        exact (PMF.map_id law).trans oneStep
      · intro next supported
        obtain ⟨history, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        rfl)
    start start rfl
  simpa only [PMF.map_id] using compared

end Vegas.RecoveryOnePacket
