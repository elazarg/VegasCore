/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.RecoveryUnpendingChoices
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Unpending actual phase decisions have no local gain -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability RecoveryProjection Filter

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
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup)
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) (RecoveryLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (RecoveryLeaks)
local notation "N" => onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) RecoveryPrior horizon
  (RecoveryScheduler)
local notation "NP" => onePacketProtocol setup (RecoveryLeaks) bounds horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup (RecoveryLeaks))
  (PMF.map RecoveryState.native (RecoveryPrior)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application setup
    (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks
    (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

open Classical in
/-- Transporting the genuine recovery unpending law through the actual local
choice equivalence leaves every phase behavioral policy unchanged. -/
theorem withLaw_eq_self_of_unpending_notOwing
    (wellFormed : setup.WellFormed) {who : Player} (site : (M).InformationSite who)
    (clear : ClearInput setup leaks site.1)
    (notFree : ¬ FreeAgent setup leaks bounds horizon scheduler ((M).agentAt site))
    (notOwing : ¬ RecoveryOnePacket.OwingAgent setup (RecoveryLeaks) bounds RecoveryPrior horizon
      (RecoveryScheduler) (projectedAgent setup leaks bounds horizon scheduler ((M).agentAt site)
          clear))
    (nonlate : ¬ KeyedAgent setup leaks bounds horizon scheduler ((M).agentAt site))
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup (RecoveryLeaks) who
      (RecoveryProjection.information (runtime setup) (RecoveryLeaks) (projectInfo site.1)) = none)
    (policy : (M).BehavioralPolicy who) (law : PMF ((M).Choice who site.1)) :
    policy.withLaw site.1 law = policy := by
  let agent := (M).agentAt site
  let recoveryPast := past.map (PhaseRecoveryProjection.playerEntry (runtime setup) leaks
      (RecoveryLeaks))
  let recoveryView := PhaseRecoveryProjection.playerView (runtime setup) leaks (RecoveryLeaks) view
  have recoveryInput : projectInfo site.1 = some (recoveryPast, recoveryView) := by
    rw [atSite]
    rfl
  have played : projectInfo site.1 ∈ (R).playedInformation who :=
    projected_input_played setup leaks bounds horizon scheduler agent clear
  have recoveryDecision : (R).IsDecisionInfo who (projectInfo site.1) := by
    let : DecidableEq ((R).InfoState who) :=
      recoveryInfoDecidableEq setup leaks bounds horizon scheduler who
    unfold InformationModel.playedInformation at played
    obtain ⟨history, member, seen⟩ := Finset.mem_image.mp played
    have running := (Finset.mem_filter.mp member).2
    let action := ((RMenu).nonempty who recoveryPast recoveryView).choose
    refine ⟨⟨history, seen⟩, running, action, ?_⟩
    rw [recoveryInput]
    change ∃ response, response ∈ (RMenu).actions who recoveryPast recoveryView ∧
      (some action : Option (recoveryApplication (runtime setup) (RecoveryLeaks)).Action) = some
          response
    exact ⟨action, ((RMenu).nonempty who recoveryPast recoveryView).choose_spec, rfl⟩
  let recoverySite : (R).InformationSite who := ⟨projectInfo site.1, recoveryDecision⟩
  have agentEq : (R).agentAt recoverySite =
      projectedAgent setup leaks bounds horizon scheduler agent clear := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext rfl)
  have recoveryNotFree : ¬ RecoveryOnePacket.FreeAgent setup (RecoveryLeaks) bounds RecoveryPrior
      horizon
      (RecoveryScheduler) ((R).agentAt recoverySite) := by
    rw [agentEq]
    exact fun free => notFree ((freeAgent_projected_iff setup leaks bounds horizon scheduler
      agent clear).mp free)
  have recoveryNotOwing : ¬ RecoveryOnePacket.OwingAgent setup (RecoveryLeaks) bounds RecoveryPrior
      horizon
      (RecoveryScheduler) ((R).agentAt recoverySite) := by
    rw [agentEq]
    exact notOwing
  have recoveryNonlate : ¬ RecoveryOnePacket.KeyedAgent setup (RecoveryLeaks) bounds RecoveryPrior
      horizon
      (RecoveryScheduler) ((R).agentAt recoverySite) := nonlate
  let equivalent := choiceEquiv setup leaks bounds horizon scheduler agent clear
  let recoveryPolicy := ((RMenu).uniformPolicy RecoveryPrior horizon (RecoveryScheduler)
      who).withLaw recoverySite.1
    ((policy site.1).map equivalent)
  have unchanged := RecoveryOnePacket.withLaw_eq_self_of_unpending_notOwing setup (RecoveryLeaks)
      bounds
    horizon (RecoveryScheduler) wellFormed recoverySite recoveryNotFree recoveryNotOwing
        recoveryNonlate recoveryInput unpending
    recoveryPolicy (law.map equivalent)
  have mapped := congrArg (fun current : (R).BehavioralPolicy who => current recoverySite.1)
      unchanged
  simp only [recoveryPolicy, BehavioralPolicy.withLaw_self] at mapped
  have lawEq : law = policy site.1 := pmf_map_injective equivalent.injective mapped
  rw [lawEq, BehavioralPolicy.withLaw_eq_self]

open Classical in
/-- The unpending phase branch has zero gain for arbitrary observations,
payoffs, policies and local laws; no service or completion premise is needed. -/
theorem localGain_eq_zero_of_unpending_notOwing
    (wellFormed : setup.WellFormed) {who : Player} (site : (M).InformationSite who)
    (clear : ClearInput setup leaks site.1)
    (notFree : ¬ FreeAgent setup leaks bounds horizon scheduler ((M).agentAt site))
    (notOwing : ¬ RecoveryOnePacket.OwingAgent setup (RecoveryLeaks) bounds RecoveryPrior horizon
      (RecoveryScheduler) (projectedAgent setup leaks bounds horizon scheduler ((M).agentAt site)
          clear))
    (nonlate : ¬ KeyedAgent setup leaks bounds horizon scheduler ((M).agentAt site))
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup (RecoveryLeaks) who
      (RecoveryProjection.information (runtime setup) (RecoveryLeaks) (projectInfo site.1)) = none)
    (fuel : Nat) {Outcome : Type} (observe :
      ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History →
          Outcome)
    (utility : Outcome → Player → ℝ) (assessment : (M).BehavioralAssessment)
    (law : PMF ((M).Choice who site.1)) :
    localGain fuel observe utility assessment site law = 0 := by
  rw [localGain]
  rw [withLaw_eq_self_of_unpending_notOwing setup leaks bounds horizon scheduler wellFormed site
    clear notFree notOwing nonlate past view atSite unpending (assessment.strategy who) law]
  simp only [assessmentComparisonWith, sub_self]

end Vegas.SequentialPhase
