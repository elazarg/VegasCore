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
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "P" => phaseApplication (runtime setup) leaks
local notation "A" => recoveryApplication (runtime setup) (recoveryLeaks setup leaks)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "rawModel" => ReactiveApplication.information (A) (oldInitial) horizon (oldScheduler)
local notation "oldProtocol" => ReactiveApplication.ResponseMenu.protocol (oldMenu) (oldInitial)
  horizon (oldScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (oldInitial) horizon (oldScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks oldLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks oldLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "oldClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

/-- At each positive clear phase site, the actual fully mixed old bounded
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
    let oldProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment
      scale positiveScale.le le_one weights
    ∃ (oldSite : (R).InformationSite who)
      (oldPositive : 0 < (R).informationMass oldProfile who oldSite),
      oldSite.1 = projectInfo site.1 ∧
      (((M).bayesBelief phaseProfile who site
        ((menu setup leaks bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler
          who site) positive).map (fun history => projection history.1.state)) =
      (((R).bayesBelief oldProfile who oldSite
        ((oldMenu).decisionInformationAntichain (oldInitial) horizon (oldScheduler) who oldSite)
        oldPositive).map (fun history => history.1.state)) := by
  classical
  dsimp only
  let : DecidableEq ((R).InfoState who) :=
    recoveryInfoDecidableEq setup leaks bounds horizon scheduler who
  let phaseProfile := componentStrategy setup leaks bounds horizon scheduler fallback assessment
    scale positiveScale.le le_one weights
  let oldProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment
    scale positiveScale.le le_one weights
  let embedded := fun player => (oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) player
    (oldProfile player)
  let oldPast := past.map (PhaseRecoveryProjection.playerEntry (runtime setup) leaks (oldLeaks))
  let oldView := PhaseRecoveryProjection.playerView (runtime setup) leaks (oldLeaks) view
  have oldInput : projectInfo site.1 = some (oldPast, oldView) := by
    simp only [siteInput, PhaseRecoveryProjection.information, Option.map_some, oldPast, oldView]
  have oldClearView : oldView.application.2 = ∅ := clear
  let agent := (M).agentAt site
  have agentClear : ClearInput setup leaks agent.2.1 := by
    change ClearInput setup leaks site.1
    rw [siteInput]
    exact clear
  have played : projectInfo site.1 ∈ (R).playedInformation who :=
    projected_input_played setup leaks bounds horizon scheduler agent agentClear
  have oldDecision : (R).IsDecisionInfo who (projectInfo site.1) := by
    unfold InformationModel.playedInformation at played
    obtain ⟨history, member, seen⟩ := Finset.mem_image.mp played
    have running := (Finset.mem_filter.mp member).2
    let action := ((oldMenu).nonempty who oldPast oldView).choose
    refine ⟨⟨history, seen⟩, running, action, ?_⟩
    rw [oldInput]
    change ∃ response, response ∈ (oldMenu).actions who oldPast oldView ∧
      (some action : Option (A).Action) = some response
    exact ⟨action, ((oldMenu).nonempty who oldPast oldView).choose_spec, rfl⟩
  let oldSite : (R).InformationSite who := ⟨projectInfo site.1, oldDecision⟩
  have oldPositive : 0 < (R).informationMass oldProfile who oldSite :=
    (R).informationMass_pos_of_fullSupport oldProfile
      (recoveryComparisonStrategy_fullSupport setup leaks bounds horizon scheduler assessment
        positiveScale le_one weights) who oldSite
  refine ⟨oldSite, oldPositive, rfl, ?_⟩
  let rawSite := (oldMenu).rawSite (oldInitial) horizon (oldScheduler) who oldSite
  have rawPositive : 0 < (rawModel).informationMass embedded who rawSite := by
    rw [← (oldMenu).informationMass_rawSite (oldInitial) horizon (oldScheduler) oldProfile]
    exact oldPositive
  let phaseCertificate := ((menu setup leaks bounds).bounded (initialLaw setup) horizon
    scheduler).wellFoundedHistories
  let oldCertificate := ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories
  let rawCertificate := ((A).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories
  let stop := fun history : (rawProtocol).History => ¬ oldClear history.state ∨
    (A).observe who history.state = projectInfo site.1
  let phaseStopped := (M).runBehavioralUntil phaseCertificate phaseProfile
    (fun history => ¬ phaseClear history.state ∨
      (A).observe who (projection history.state) = projectInfo site.1)
    ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).initHistory
  let oldStopped := (R).runBehavioralUntil oldCertificate oldProfile
    (fun history => stop ((oldMenu).toRawHistory (oldInitial) horizon (oldScheduler) history))
    (oldProtocol).initHistory
  let rawStopped := (rawModel).runBehavioralUntil rawCertificate embedded stop
    (rawProtocol).initHistory
  have phaseLaw : phaseStopped.map (fun history => projection history.state) =
      oldStopped.map History.state :=
    component_comparison_run_until_exclusion_or_guard_map_state setup leaks bounds horizon
      scheduler fallback assessment scale positiveScale.le le_one weights
      (fun state => (A).observe who state = projectInfo site.1) _ _ rfl
  have embeddedLaw := congrArg (PMF.map History.state)
    ((oldMenu).runBehavioralUntil_embed (oldInitial) horizon (oldScheduler) rawCertificate
      oldCertificate oldProfile stop (oldProtocol).initHistory)
  rw [PMF.map_comp] at embeddedLaw
  have laws : phaseStopped.map (fun history => projection history.state) =
      rawStopped.map History.state := phaseLaw.trans embeddedLaw
  have phasePosterior := SequentialPhaseRecoveryPolicy.phase_bayesBelief_eq_stopped_recovery_state
    setup.program (runtime setup) leaks (menu setup leaks bounds) bounds
    (PhaseCount.normalized_onePacket_included (runtime setup) leaks bounds)
    (setup.initialLaw.map setup.eventInputs) horizon scheduler phaseProfile who site past view
    siteInput clear positive
  have rawPosterior := SequentialPhaseRecoveryPolicy.recovery_bayesBelief_eq_stopped_state
    setup.program (runtime setup) leaks (setup.initialLaw.map setup.eventInputs) horizon scheduler
    embedded who rawSite oldPast oldView oldInput oldClearView rawPositive
  dsimp only at phasePosterior rawPosterior
  change fiberPosterior (phaseStopped.map (fun history => projection history.state))
    ((A).observe who) (projectInfo site.1) = _ at phasePosterior
  change fiberPosterior (rawStopped.map History.state) ((A).observe who)
    (projectInfo site.1) = _ at rawPosterior
  have beliefs := congrArg (PMF.map (fun history => history.1.state))
    ((oldMenu).bayesBelief_rawSite (oldInitial) horizon (oldScheduler) oldProfile who oldSite
      oldPositive)
  rw [PMF.map_comp] at beliefs
  rw [laws] at phasePosterior
  exact (phasePosterior.symm.trans rawPosterior).trans beliefs.symm

end Vegas.SequentialPhase
