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
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "Initial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (oldLeaks)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) Initial horizon
  (oldScheduler)
local notation "NP" => onePacketProtocol setup (oldLeaks) bounds horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup (oldLeaks))
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application setup (oldLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local instance unpendingPosteriorComparisonHistory : Fintype ((RMenu).protocol
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).History :=
  sourceHistoryFintype setup leaks bounds horizon scheduler

local instance unpendingPosteriorComparisonInformation (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds
      ((Vegas.initialLaw setup).map (fun native =>
        (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).InfoState who) :=
  sourceInfoDecidableEq setup leaks bounds horizon scheduler who

local instance unpendingPosteriorComparisonNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance unpendingPosteriorNativeInformation (who : Player) :
    DecidableEq ((N).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

local instance unpendingPosteriorRecoveryNature :
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) (oldScheduler) :=
  recoveryNature setup leaks scheduler

local instance unpendingPosteriorNativeHistory : Fintype (NP).History :=
  @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (NMenu) (Vegas.initialLaw setup)
    horizon (NativeScheduler) inferInstance (nativeNature setup leaks scheduler)

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq


open Classical in
/-- Transporting the genuine recovery unpending law through the actual local
choice equivalence leaves every phase behavioral policy unchanged. -/
theorem withLaw_eq_self_of_unpending_notOwing
    (wellFormed : setup.WellFormed) {who : Player} (site : (M).InformationSite who)
    (clear : ClearInput setup leaks site.1)
    (notFree : ¬ FreeAgent setup leaks bounds horizon scheduler ((M).agentAt site))
    (notOwing : ¬ RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler) (projectedAgent setup leaks bounds horizon scheduler ((M).agentAt site) clear))
    (nonlate : ¬ KeyedAgent setup leaks bounds horizon scheduler ((M).agentAt site))
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup (oldLeaks) who
      (RecoveryProjection.information (runtime setup) (oldLeaks) (projectInfo site.1)) = none)
    (policy : (M).BehavioralPolicy who) (law : PMF ((M).Choice who site.1)) :
    policy.withLaw site.1 law = policy := by
  let agent := (M).agentAt site
  let oldPast := past.map (PhaseRecoveryProjection.playerEntry (runtime setup) leaks (oldLeaks))
  let oldView := PhaseRecoveryProjection.playerView (runtime setup) leaks (oldLeaks) view
  have oldInput : projectInfo site.1 = some (oldPast, oldView) := by
    rw [atSite]
    rfl
  have played : projectInfo site.1 ∈ (R).playedInformation who :=
    projected_input_played setup leaks bounds horizon scheduler agent clear
  have oldDecision : (R).IsDecisionInfo who (projectInfo site.1) := by
    let : DecidableEq ((R).InfoState who) :=
      recoveryInfoDecidableEq setup leaks bounds horizon scheduler who
    unfold InformationModel.playedInformation at played
    obtain ⟨history, member, seen⟩ := Finset.mem_image.mp played
    have running := (Finset.mem_filter.mp member).2
    let action := ((RMenu).nonempty who oldPast oldView).choose
    refine ⟨⟨history, seen⟩, running, action, ?_⟩
    rw [oldInput]
    change ∃ response, response ∈ (RMenu).actions who oldPast oldView ∧
      (some action : Option (recoveryApplication (runtime setup) (oldLeaks)).Action) = some response
    exact ⟨action, ((RMenu).nonempty who oldPast oldView).choose_spec, rfl⟩
  let oldSite : (R).InformationSite who := ⟨projectInfo site.1, oldDecision⟩
  have agentEq : (R).agentAt oldSite =
      projectedAgent setup leaks bounds horizon scheduler agent clear := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext rfl)
  have oldNotFree : ¬ RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler) ((R).agentAt oldSite) := by
    rw [agentEq]
    exact fun free => notFree ((freeAgent_projected_iff setup leaks bounds horizon scheduler
      agent clear).mp free)
  have oldNotOwing : ¬ RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler) ((R).agentAt oldSite) := by
    rw [agentEq]
    exact notOwing
  have oldNonlate : ¬ RecoveryOnePacket.KeyedAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler) ((R).agentAt oldSite) := nonlate
  let equivalent := choiceEquiv setup leaks bounds horizon scheduler agent clear
  let oldPolicy := ((RMenu).uniformPolicy Initial horizon (oldScheduler) who).withLaw oldSite.1
    ((policy site.1).map equivalent)
  have unchanged := RecoveryOnePacket.withLaw_eq_self_of_unpending_notOwing setup (oldLeaks) bounds
    horizon (oldScheduler) wellFormed oldSite oldNotFree oldNotOwing oldNonlate oldInput unpending
    oldPolicy (law.map equivalent)
  have mapped := congrArg (fun current : (R).BehavioralPolicy who => current oldSite.1) unchanged
  simp only [oldPolicy, BehavioralPolicy.withLaw_self] at mapped
  have lawEq : law = policy site.1 := pmf_map_injective equivalent.injective mapped
  rw [lawEq, BehavioralPolicy.withLaw_eq_self]

open Classical in
/-- The unpending phase branch has zero gain for arbitrary observations,
payoffs, policies and local laws; no service or completion premise is needed. -/
theorem localGain_eq_zero_of_unpending_notOwing
    (wellFormed : setup.WellFormed) {who : Player} (site : (M).InformationSite who)
    (clear : ClearInput setup leaks site.1)
    (notFree : ¬ FreeAgent setup leaks bounds horizon scheduler ((M).agentAt site))
    (notOwing : ¬ RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler) (projectedAgent setup leaks bounds horizon scheduler ((M).agentAt site) clear))
    (nonlate : ¬ KeyedAgent setup leaks bounds horizon scheduler ((M).agentAt site))
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup (oldLeaks) who
      (RecoveryProjection.information (runtime setup) (oldLeaks) (projectInfo site.1)) = none)
    (fuel : Nat) {Outcome : Type} (observe :
      ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History → Outcome)
    (utility : Outcome → Player → ℝ) (assessment : (M).BehavioralAssessment)
    (law : PMF ((M).Choice who site.1)) :
    localGain fuel observe utility assessment site law = 0 := by
  rw [localGain]
  rw [withLaw_eq_self_of_unpending_notOwing setup leaks bounds horizon scheduler wellFormed site
    clear notFree notOwing nonlate past view atSite unpending (assessment.strategy who) law]
  simp only [assessmentComparisonWith, sub_self]

end Vegas.SequentialPhase
