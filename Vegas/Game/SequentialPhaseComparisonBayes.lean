/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonStopped
import Interaction.ReactiveResponseBelief
import Interaction.ReactiveResponseStopped

/-! # Bayes state beliefs of actual phase and bounded recovery comparisons -/

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

local notation "P" => phaseApplication (runtime setup) leaks
local notation "A" => recoveryApplication (runtime setup) (recoveryLeaks setup leaks)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu (runtime setup) (RecoveryLeaks) bounds
local notation "rawModel" => ReactiveApplication.information (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "RecoveryProtocol" => ReactiveApplication.ResponseMenu.protocol (RecoveryMenu)
    (RecoveryPrior)
  horizon (RecoveryScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks
    RecoveryLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks
    RecoveryLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "RecoveryClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- At each positive clear phase site, the actual fully mixed recovery bounded
comparison has a positive decision site with exactly the same Bayes belief on
complete physical recovery states. No beliefs over whole histories are identified. -/
theorem component_comparison_bayes_state_eq
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (positiveScale : 0 < scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (who : Player) (site : (M).InformationSite who)
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (positive : 0 < (M).informationMass
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale
        positiveScale.le le_one weights) who site) :
    let phaseProfile := componentStrategy setup leaks bounds horizon scheduler fallback assessment
      scale positiveScale.le le_one weights
    let recoveryProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler
        assessment
      scale positiveScale.le le_one weights
    ∃ (recoverySite : (R).InformationSite who)
      (recoveryPositive : 0 < (R).informationMass recoveryProfile who recoverySite),
      recoverySite.1 = projectInfo site.1 ∧
      (((M).bayesBelief phaseProfile who site
        ((menu setup leaks bounds).decisionInformationAntichain (phaseInitialLaw setup) horizon
            scheduler
          who site) positive).map (fun history => projection history.1.state)) =
      (((R).bayesBelief recoveryProfile who recoverySite
        ((RecoveryMenu).decisionInformationAntichain (RecoveryPrior) horizon (RecoveryScheduler) who
            recoverySite)
        recoveryPositive).map (fun history => history.1.state)) := by
  classical
  dsimp only
  let : DecidableEq ((R).InfoState who) :=
    recoveryInfoDecidableEq setup leaks bounds horizon scheduler who
  let phaseProfile := componentStrategy setup leaks bounds horizon scheduler fallback assessment
    scale positiveScale.le le_one weights
  let recoveryProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment
    scale positiveScale.le le_one weights
  let embedded := fun player => (RecoveryMenu).embedPolicy (RecoveryPrior) horizon
      (RecoveryScheduler) player
    (recoveryProfile player)
  let recoveryPast := past.map (PhaseRecoveryProjection.playerEntry (runtime setup) leaks
      (RecoveryLeaks))
  let recoveryView := PhaseRecoveryProjection.playerView (runtime setup) leaks (RecoveryLeaks) view
  have recoveryInput : projectInfo site.1 = some (recoveryPast, recoveryView) := by
    simp only [siteInput, PhaseRecoveryProjection.information, Option.map_some, recoveryPast,
        recoveryView]
  have recoveryClearView : recoveryView.application.2 = ∅ := clear
  let agent := (M).agentAt site
  have agentClear : ClearInput setup leaks agent.2.1 := by
    change ClearInput setup leaks site.1
    rw [siteInput]
    exact clear
  have played : projectInfo site.1 ∈ (R).playedInformation who :=
    projected_input_played setup leaks bounds horizon scheduler agent agentClear
  have recoveryDecision : (R).IsDecisionInfo who (projectInfo site.1) := by
    unfold InformationModel.playedInformation at played
    obtain ⟨history, member, seen⟩ := Finset.mem_image.mp played
    have running := (Finset.mem_filter.mp member).2
    let action := ((RecoveryMenu).nonempty who recoveryPast recoveryView).choose
    refine ⟨⟨history, seen⟩, running, action, ?_⟩
    rw [recoveryInput]
    change ∃ response, response ∈ (RecoveryMenu).actions who recoveryPast recoveryView ∧
      (some action : Option (A).Action) = some response
    exact ⟨action, ((RecoveryMenu).nonempty who recoveryPast recoveryView).choose_spec, rfl⟩
  let recoverySite : (R).InformationSite who := ⟨projectInfo site.1, recoveryDecision⟩
  have recoveryPositive : 0 < (R).informationMass recoveryProfile who recoverySite :=
    (R).informationMass_pos_of_fullSupport recoveryProfile
      (recoveryComparisonStrategy_fullSupport setup leaks bounds horizon scheduler assessment
        positiveScale le_one weights) who recoverySite
  refine ⟨recoverySite, recoveryPositive, rfl, ?_⟩
  let rawSite := (RecoveryMenu).rawSite (RecoveryPrior) horizon (RecoveryScheduler) who recoverySite
  have rawPositive : 0 < (rawModel).informationMass embedded who rawSite := by
    rw [← (RecoveryMenu).informationMass_rawSite (RecoveryPrior) horizon (RecoveryScheduler)
        recoveryProfile]
    exact recoveryPositive
  let phaseCertificate := ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
    scheduler).wellFoundedHistories
  let recoveryCertificate := ((RecoveryMenu).bounded (RecoveryPrior) horizon
      (RecoveryScheduler)).wellFoundedHistories
  let rawCertificate := ((A).bounded (RecoveryPrior) horizon
      (RecoveryScheduler)).wellFoundedHistories
  let stop := fun history : (rawProtocol).History => ¬ RecoveryClear history.state ∨
    (A).observe who history.state = projectInfo site.1
  let phaseStopped := (M).runBehavioralUntil phaseCertificate phaseProfile
    (fun history => ¬ phaseClear history.state ∨
      (A).observe who (projection history.state) = projectInfo site.1)
    ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).initHistory
  let recoveryStopped := (R).runBehavioralUntil recoveryCertificate recoveryProfile
    (fun history => stop ((RecoveryMenu).toRawHistory (RecoveryPrior) horizon (RecoveryScheduler)
        history))
    (RecoveryProtocol).initHistory
  let rawStopped := (rawModel).runBehavioralUntil rawCertificate embedded stop
    (rawProtocol).initHistory
  have phaseLaw : phaseStopped.map (fun history => projection history.state) =
      recoveryStopped.map History.state :=
    component_comparison_run_until_exclusion_or_guard_map_state setup leaks bounds horizon
      scheduler fallback assessment scale positiveScale.le le_one weights
      (fun state => (A).observe who state = projectInfo site.1) _ _ rfl
  have embeddedLaw := congrArg (PMF.map History.state)
    ((RecoveryMenu).runBehavioralUntil_embed (RecoveryPrior) horizon (RecoveryScheduler)
        rawCertificate
      recoveryCertificate recoveryProfile stop (RecoveryProtocol).initHistory)
  rw [PMF.map_comp] at embeddedLaw
  have laws : phaseStopped.map (fun history => projection history.state) =
      rawStopped.map History.state := phaseLaw.trans embeddedLaw
  have phasePosterior := SequentialPhaseRecoveryPolicy.phase_bayesBelief_eq_stopped_recovery_state
    setup.program (runtime setup) leaks (menu setup leaks bounds) bounds
    (PhaseCount.normalized_onePacket_included (runtime setup) leaks bounds)
    (setup.initialLaw.map setup.eventInputs) horizon scheduler phaseProfile who site past view
    siteInput clear positive
  have priorEq : (setup.initialLaw.map setup.eventInputs).map
      (fun input => (RecoveryState.mk (EventGraphRuntime.State.initial input) ∅ :
        RecoveryState (graph setup))) = RecoveryPrior := by
    simp only [recoveryInitialLaw, Vegas.initialLaw, serviceInitialLaw, PMF.map_comp,
      Function.comp_def]
  have rawProducer := SequentialPhaseRecoveryPolicy.recovery_bayesBelief_eq_stopped_state
    setup.program (runtime setup) leaks (setup.initialLaw.map setup.eventInputs) horizon scheduler
  erw [priorEq] at rawProducer
  have rawPosterior := rawProducer embedded who rawSite recoveryPast recoveryView recoveryInput
      recoveryClearView
    rawPositive
  dsimp only at phasePosterior rawPosterior
  change fiberPosterior (phaseStopped.map (fun history => projection history.state))
    ((A).observe who) (projectInfo site.1) = _ at phasePosterior
  change fiberPosterior (rawStopped.map History.state) ((A).observe who)
    (projectInfo site.1) = _ at rawPosterior
  have beliefs := congrArg (PMF.map (fun history => history.1.state))
    ((RecoveryMenu).bayesBelief_rawSite (RecoveryPrior) horizon (RecoveryScheduler) recoveryProfile
        who recoverySite
      recoveryPositive)
  rw [PMF.map_comp] at beliefs
  rw [laws] at phasePosterior
  exact (phasePosterior.symm.trans rawPosterior).trans beliefs.symm

end Vegas.SequentialPhase
