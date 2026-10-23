/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeClearBelief
import Vegas.Game.RecoveryNativePrior
import Vegas.Pending.ExclusionBoundedBelief

/-! # Actual recovery and native comparison beliefs at clear sites

The same completed strategy weights determine both laws. Existing full-fiber
Bayes transport and exact prior equality identify entire raw history laws.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
  Interaction

private theorem informationMass_prior_eq
    {Player : Type} [DecidableEq Player] [Fintype Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler)
    (profile : ∀ who, (menu.information first horizon scheduler).BehavioralPolicy who)
    (who : Player) (input : app.Info)
    (firstDecision : (menu.information first horizon scheduler).IsDecisionInfo who input)
    (secondDecision : (menu.information second horizon scheduler).IsDecisionInfo who input) :
    (menu.information first horizon scheduler).informationMass profile who ⟨input, firstDecision⟩ =
      (menu.information second horizon scheduler).informationMass
        (fun player localInput => (profile player localInput).map (Equiv.cast
          (congrArg (fun initial => (menu.information initial horizon scheduler).Choice player
            localInput) same))) who ⟨input, secondDecision⟩ := by
  subst second
  simp only [Equiv.cast_refl, Equiv.coe_refl, PMF.map_id]

private theorem bayesBelief_raw_prior_eq
    {Player : Type} [DecidableEq Player] [Fintype Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler)
    (profile : ∀ who, (menu.information first horizon scheduler).BehavioralPolicy who)
    (who : Player) (input : app.Info)
    (firstDecision : (menu.information first horizon scheduler).IsDecisionInfo who input)
    (secondDecision : (menu.information second horizon scheduler).IsDecisionInfo who input)
    (positive : 0 < (menu.information first horizon scheduler).informationMass profile who
      ⟨input, firstDecision⟩) :
    let translated : ∀ player,
        (menu.information second horizon scheduler).BehavioralPolicy player :=
      fun player localInput => (profile player localInput).map (Equiv.cast
        (congrArg (fun initial => (menu.information initial horizon scheduler).Choice player
          localInput) same))
    let targetPositive :
        0 < (menu.information second horizon scheduler).informationMass translated who
          ⟨input, secondDecision⟩ := by
      exact Eq.mp (congrArg (fun mass : ENNReal => 0 < mass)
        (informationMass_prior_eq menu same horizon scheduler profile who input firstDecision
          secondDecision)) positive
    ((menu.information first horizon scheduler).bayesBelief profile who ⟨input, firstDecision⟩
      (menu.decisionInformationAntichain first horizon scheduler who ⟨input, firstDecision⟩)
      positive).map (fun history =>
        Equiv.cast
          (congrArg (fun initial => (app.protocol initial horizon scheduler).History) same)
          (menu.toRawHistory first horizon scheduler history.1)) =
      ((menu.information second horizon scheduler).bayesBelief translated who
        ⟨input, secondDecision⟩
        (menu.decisionInformationAntichain second horizon scheduler who ⟨input, secondDecision⟩)
        targetPositive).map (fun history =>
          menu.toRawHistory second horizon scheduler history.1) := by
  subst second
  simp only [Equiv.cast_refl, Equiv.coe_refl, PMF.map_id]
  rfl

open SourceProgram GameTheory.Protocol.InformationModel EventGraphRuntime RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

/-- The actual recovery belief and its same-weight native comparison have
exactly the same law on complete projected raw histories at clear sites. -/
theorem recovery_belief_eq_nativeComparison [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (R).Policy who)
    (assessment : (R).BehavioralAssessment)
    (assembled : assessment.strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : BehavioralAssessment.IsBayesConsistent (R) assessment
      ((RMenu).decisionInformationAntichain Initial horizon scheduler))
    (who : Player) (reference : (application setup leaks).Control)
    (active : reference.actor = some who)
    (valid : PublicExclusionRecord (RecoveryState.mk reference.execution.application ∅))
    (nativeDecision : (N).IsDecisionInfo who
      ((application setup leaks).observe who (some reference)))
    (recoveryDecision : (R).IsDecisionInfo who (liftInformation (runtime setup) leaks
      ((application setup leaks).observe who (some reference)))) :
    let nativeSite : (N).InformationSite who :=
      ⟨(application setup leaks).observe who (some reference), nativeDecision⟩
    let recoverySite : (R).InformationSite who :=
      ⟨liftInformation (runtime setup) leaks
        ((application setup leaks).observe who (some reference)), recoveryDecision⟩
    (assessment.belief who recoverySite).map (fun history =>
      Equiv.cast (congrArg (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
        ((application setup leaks).protocol law horizon (NativeScheduler)).History)
          (initialLaw_native setup))
        (informationHistoryEquiv (runtime setup) leaks Initial (initialLaw_initialized setup)
          horizon scheduler who reference active valid
          ((RMenu).rawInformationHistory Initial horizon scheduler who recoverySite history)).1) =
      ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n).belief who nativeSite).map (fun history =>
          (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) history.1) := by
  dsimp only
  let input := (application setup leaks).observe who (some reference)
  let nativeSite : (N).InformationSite who := ⟨input, nativeDecision⟩
  let recoverySite : (R).InformationSite who :=
    ⟨liftInformation (runtime setup) leaks input, recoveryDecision⟩
  let genericInitial := (Initial).map RecoveryState.native
  let genericModel := (NMenu).information genericInitial horizon (NativeScheduler)
  let genericRaw := (application setup leaks).information genericInitial horizon (NativeScheduler)
  let genericDecision : genericModel.IsDecisionInfo who input :=
    Eq.mpr (congrArg (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).information law horizon (NativeScheduler)).IsDecisionInfo who input)
        (initialLaw_native setup)) nativeDecision
  let genericSite : genericModel.InformationSite who := ⟨input, genericDecision⟩
  let profile := boundedNativeProfile (runtime setup) leaks bounds Initial horizon scheduler
    assessment.strategy
  let translated : ∀ player, (N).BehavioralPolicy player := fun player localInput =>
    (profile player localInput).map (Equiv.cast (congrArg
      (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
        ((NMenu).information law horizon (NativeScheduler)).Choice player localInput)
          (initialLaw_native setup)))
  have translation : translated =
      sourceNativeProfile setup leaks bounds horizon scheduler assessment.strategy := by
    funext player localInput
    exact (sourceNativeProfile_eq_cast setup leaks bounds horizon scheduler assessment.strategy
      player localInput).symm
  have comparisonMass := informationMass_nativeComparison_of_clear setup leaks bounds horizon
    scheduler sequence scale positive le_one weights n fallback assessment.strategy assembled who
    reference active valid nativeSite rfl
  have projectedPositive :
      0 < (N).informationMass (sourceNativeProfile setup leaks bounds horizon scheduler
        assessment.strategy) who nativeSite :=
    Eq.mp (congrArg (fun mass : ENNReal => 0 < mass) comparisonMass)
      ((N).informationMass_pos_of_fullSupport _ (nativeComparisonStrategy_fullSupport setup leaks
        bounds horizon scheduler sequence scale positive le_one weights n) who nativeSite)
  have translatedPositive : 0 < (N).informationMass translated who nativeSite :=
    Eq.mpr (congrArg (fun strategy => 0 < (N).informationMass strategy who nativeSite) translation)
      projectedPositive
  have priorMass : genericModel.informationMass profile who genericSite =
      (N).informationMass translated who nativeSite :=
    informationMass_prior_eq (NMenu) (initialLaw_native setup) horizon (NativeScheduler) profile who
      input genericDecision nativeDecision
  have genericPositive : 0 < genericModel.informationMass profile who genericSite :=
    Eq.mpr (congrArg (fun mass : ENNReal => 0 < mass) priorMass) translatedPositive
  have recoveryMass : (R).informationMass assessment.strategy who recoverySite =
      genericModel.informationMass profile who genericSite :=
    bounded_informationMass_liftedInformationSite (runtime setup) leaks bounds Initial
      (initialLaw_initialized setup) horizon scheduler who reference active valid genericDecision
      recoveryDecision assessment.strategy
  have recoveryPositive : 0 < (R).informationMass assessment.strategy who recoverySite :=
    Eq.mpr (congrArg (fun mass : ENNReal => 0 < mass) recoveryMass) genericPositive
  let recoveryBelief := (R).bayesBelief assessment.strategy who recoverySite
    ((RMenu).decisionInformationAntichain Initial horizon scheduler who recoverySite)
    recoveryPositive
  have actualBelief : assessment.belief who recoverySite = recoveryBelief :=
    (InformationModel.BehavioralAssessment.isBayesConsistentAt_iff (R) assessment who recoverySite
      ((RMenu).decisionInformationAntichain Initial horizon scheduler who recoverySite)
      recoveryPositive).mp (bayes who recoverySite recoveryPositive)
  let genericBelief := genericModel.bayesBelief profile who genericSite
    ((NMenu).decisionInformationAntichain genericInitial horizon (NativeScheduler) who genericSite)
    genericPositive
  let fiberMap : (R).InformationHistory who recoverySite.1 →
      genericRaw.InformationHistory who input := fun history =>
    informationHistoryEquiv (runtime setup) leaks Initial (initialLaw_initialized setup) horizon
      scheduler who reference active valid
      ((RMenu).rawInformationHistory Initial horizon scheduler who recoverySite history)
  have transfer : (assessment.belief who recoverySite).map fiberMap =
      genericBelief.map
        ((NMenu).rawInformationHistory genericInitial horizon (NativeScheduler) who genericSite) :=
    (congrArg (fun law => law.map fiberMap) actualBelief).trans
      (bounded_bayesBelief_liftedInformationSite (runtime setup) leaks bounds Initial
        (initialLaw_initialized setup) horizon scheduler who reference active valid genericDecision
        recoveryDecision assessment.strategy genericPositive)
  let rawCast :
      ((application setup leaks).protocol genericInitial horizon (NativeScheduler)).History ≃
      ((application setup leaks).protocol (initialLaw setup) horizon (NativeScheduler)).History :=
    Equiv.cast (congrArg (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
      ((application setup leaks).protocol law horizon (NativeScheduler)).History)
        (initialLaw_native setup))
  let projectRaw : genericRaw.InformationHistory who input →
      ((application setup leaks).protocol (initialLaw setup) horizon (NativeScheduler)).History :=
    fun history => rawCast history.1
  let projectedBelief := (N).bayesBelief translated who nativeSite
    ((NMenu).decisionInformationAntichain (initialLaw setup) horizon (NativeScheduler) who
      nativeSite)
    translatedPositive
  have priorBelief : genericBelief.map (fun history =>
        rawCast ((NMenu).toRawHistory genericInitial horizon (NativeScheduler) history.1)) =
      projectedBelief.map (fun history =>
        (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) history.1) :=
    bayesBelief_raw_prior_eq (NMenu) (initialLaw_native setup) horizon (NativeScheduler) profile who
      input genericDecision nativeDecision genericPositive
  have comparisonBelief :
      (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n).belief who nativeSite = projectedBelief := by
    ext history
    rw [InformationModel.bayesBelief_apply]
    have formula := nativeComparison_bayes_formula_of_clear setup leaks bounds horizon scheduler
      sequence scale positive le_one weights n fallback assessment.strategy assembled who reference
      active valid nativeSite rfl history
    exact formula.trans (congrArg (fun strategy =>
      (N).historyReachWeight strategy history.1 / (N).informationMass strategy who nativeSite)
        translation.symm)
  change (assessment.belief who recoverySite).map (projectRaw ∘ fiberMap) =
    ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
      weights n).belief who nativeSite).map (fun history =>
        (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) history.1)
  calc
    _ = ((assessment.belief who recoverySite).map fiberMap).map projectRaw :=
      (PMF.map_comp (p := assessment.belief who recoverySite) (f := fiberMap) projectRaw).symm
    _ = (genericBelief.map
        ((NMenu).rawInformationHistory genericInitial horizon (NativeScheduler) who
          genericSite)).map projectRaw := congrArg (fun law => law.map projectRaw) transfer
    _ = genericBelief.map (fun history =>
        rawCast ((NMenu).toRawHistory genericInitial horizon (NativeScheduler) history.1)) :=
      PMF.map_comp (p := genericBelief)
        (f := (NMenu).rawInformationHistory genericInitial horizon (NativeScheduler) who
          genericSite)
        projectRaw
    _ = projectedBelief.map (fun history =>
        (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) history.1) := priorBelief
    _ = _ := congrArg (fun law => law.map (fun history =>
      (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) history.1))
        comparisonBelief.symm

end Vegas.RecoveryOnePacket
