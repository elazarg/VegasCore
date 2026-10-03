/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionPreservation
import Vegas.Examples.LateResolutionExtensionResources
import Vegas.Examples.LateResolutionCompletedContinuation
import GameTheory.Analysis.Protocol.RestrictionExtension

/-! # Rational completion in the complete effective response menu

The additional first responses are bounded by the actual clean TRUE decision,
which attains the global upper payoff. After a recorded first decision the
typed configuration is immutable, and the actual clean retained continuation
attains its recorded base utility. At the late unrecorded input every
effective continuation has nonpositive payoff. These comparisons impose no
detection bound.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

abbrev effectiveMenu (bounds : MessageBounds nativeGraph) : app.ResponseMenu :=
  bounds.menu (runtime setup) leaks

abbrev effectiveModel (bounds : MessageBounds nativeGraph) :=
  (effectiveMenu bounds).information (initialLaw setup) horizon scheduler

def effectiveRestriction (bounds : MessageBounds nativeGraph) :
    (nativeModel bounds).ActionRestriction (effectiveModel bounds) :=
  (bounds.riskMenu_in_effective (runtime setup) leaks bound).actionRestriction
    (initialLaw setup) horizon scheduler

open Classical in
def retainedComparator (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (who : Player) (site : (nativeModel bounds).InformationSite who) :
    PMF ((nativeModel bounds).Choice who site.1) := by
  have own : who = owner := Subsingleton.elim _ _
  subst who
  by_cases early : site.1 = some (firstExecution.recall owner, firstExecution.observe app owner)
  · refine PMF.pure ⟨some (lateResponse firstCandidate true), ?_⟩
    rw [early]
    exact ⟨lateResponse firstCandidate true, first_response_available bounds covers true, rfl⟩
  · by_cases late : site.1 =
        some (secondWaitExecution.recall owner, secondWaitExecution.observe app owner)
    · refine PMF.pure ⟨some (lateResponse firstCandidate false), ?_⟩
      rw [late]
      exact ⟨lateResponse firstCandidate false, second_wait_withhold_available bounds, rfl⟩
    · exact ((nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler).strategy
        owner site.1

theorem retainedComparator_first (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (site : (nativeModel bounds).InformationSite owner)
    (early : site.1 = some (firstExecution.recall owner, firstExecution.observe app owner)) :
    (retainedComparator bounds covers owner site).map Subtype.val =
      PMF.pure (some (lateResponse firstCandidate true)) := by
  classical
  simp only [retainedComparator, dite_eq_left early, PMF.pure_map]

theorem retainedComparator_second_wait (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (site : (nativeModel bounds).InformationSite owner)
    (late : site.1 =
      some (secondWaitExecution.recall owner, secondWaitExecution.observe app owner)) :
    (retainedComparator bounds covers owner site).map Subtype.val =
      PMF.pure (some (lateResponse firstCandidate false)) := by
  classical
  have early : site.1 ≠ some (firstExecution.recall owner, firstExecution.observe app owner) := by
    rw [late]
    exact Ne.symm first_info_ne_second_wait
  simp only [retainedComparator, dite_eq_right early, dite_eq_left late, PMF.pure_map]

theorem completed_risk_continuation_value (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (disclose : Bool)
    (current : history.state = some ⟨4, some owner, secondDecisionExecution disclose⟩)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) :
    expect ((nativeModel bounds).runBehavioralFrom profile 21 history)
      (fun final => auditedUtility sample deposit final.state owner) =
        if disclose then 1 else 0 := by
  have chosen : (profile owner (some ((secondDecisionExecution disclose).recall owner,
      (secondDecisionExecution disclose).observe app owner))).map Subtype.val =
        PMF.pure (some (⟨none⟩ : app.Action)) := second_decision_choice_law bounds disclose _
  rw [late_native_response_value (nativeMenu bounds) profile history
    (secondDecisionExecution disclose) current (by rfl) ⟨none⟩ chosen
    (fun state => auditedUtility sample deposit state owner),
    first_completed_rounds, PMF.pure_map, expect_pure,
    first_endpoint_value disclose sample authentic deposit]

theorem effective_late_continuation_le_zero (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (effectiveModel bounds).BehavioralPolicy who)
    (history : ((effectiveMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (execution : app.Execution) (current : history.state = some ⟨4, some owner, execution⟩)
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) :
    expect ((effectiveModel bounds).runBehavioralFrom profile 21 history)
      (fun final => auditedUtility sample deposit final.state owner) ≤ 0 := by
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) 0
  intro final supported
  have reached : final.state ∈
      (((effectiveModel bounds).runBehavioralFrom profile 21 history).map
        ExecutionProtocol.History.state).support := by
    rw [PMF.support_map]
    exact Set.mem_image_of_mem _ supported
  rw [late_native_run_state (effectiveMenu bounds) profile history execution current position,
    PMF.support_bind] at reached
  obtain ⟨action, _, finished⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨last, continued, same⟩ := PMF.support_map .. ▸ finished
  have failed := late_raw_response_failed execution
    ((effectiveMenu bounds).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.trace)) position ready entered clock (action.getD ⟨none⟩) last continued
  have base := baseUtility_failure (⟨0, none, last⟩ : app.Control) failed
  change baseUtility setup leaks sourceUtility (app.finished last) owner = 0 at base
  have charge := (GameTheory.Enforcement.TerminalAudit.charge_mem_Icc
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
    (app.finished last) owner).1
  rw [← same]
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility
  rw [base]
  exact sub_nonpos.mpr (mul_nonneg charge nonnegative)

theorem effectiveCertificate (bounds : MessageBounds nativeGraph) :
    ((effectiveMenu bounds).protocol (initialLaw setup) horizon scheduler).WellFoundedHistories :=
  ((effectiveMenu bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories

theorem effective_embedded_audited_value (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (who : Player)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History) :
    auditedUtility sample deposit ((effectiveRestriction bounds).history history).state who =
      auditedUtility sample deposit history.state who := by
  exact congrArg (fun state => auditedUtility sample deposit state who)
    ((bounds.riskMenu_in_effective (runtime setup) leaks bound).history_state
      (initialLaw setup) horizon scheduler history)

open Classical in
theorem effective_whole_continuation_comparison (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (sourceProfile : ∀ who, (nativeModel bounds).BehavioralPolicy who)
    (targetProfile : ∀ who, (effectiveModel bounds).BehavioralPolicy who)
    (who : Player) (site : (nativeModel bounds).InformationSite who)
    (history : (nativeModel bounds).InformationHistory who site.1) :
    expect ((effectiveModel bounds).runBehavioralFrom targetProfile 21
      ((effectiveRestriction bounds).history history.1))
      (fun final => auditedUtility sample deposit final.state who) ≤
    expect ((nativeModel bounds).runBehavioralFrom
      (Profile.update (sig := (nativeModel bounds).behavioralSignature) sourceProfile who
        ((sourceProfile who).withLaw site.1 (retainedComparator bounds covers who site)))
      21 history.1) (fun final => auditedUtility sample deposit final.state who) := by
  have own : who = owner := Subsingleton.elim _ _
  subst who
  rcases native_decision_site_cases bounds site with early | late | ⟨disclose, completed⟩
  · let actual : (nativeModel bounds).InformationHistory owner (firstSite bounds).1 :=
      ⟨history.1, history.2.trans early⟩
    have chosen : ((Profile.update (sig := (nativeModel bounds).behavioralSignature)
        sourceProfile owner ((sourceProfile owner).withLaw site.1
          (retainedComparator bounds covers owner site))) owner
        (some (firstExecution.recall owner, firstExecution.observe app owner))).map
          Subtype.val = PMF.pure (some (lateResponse firstCandidate true)) := by
      rw [← early, Profile.update_same, InformationModel.BehavioralPolicy.withLaw_self]
      exact retainedComparator_first bounds covers site early
    rw [first_native_response_value bounds _ history.1
      (first_information_resources bounds actual) true chosen sample authentic deposit]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1
    intro final _
    exact (auditedUtility_bounds sample deposit nonnegative final.state owner).2
  · obtain ⟨trace⟩ := second_wait_site_trace bounds site late
    let actual : (nativeModel bounds).InformationHistory owner
        (lateSite bounds secondWaitExecution trace).1 := ⟨history.1, history.2.trans late⟩
    obtain ⟨execution, current, position, clock, ready, entered, empty⟩ :=
      late_information_resources bounds secondWaitExecution trace second_wait_ready
        second_wait_entered second_wait_clock second_wait_empty actual
    have observed : some (execution.recall owner, execution.observe app owner) = site.1 :=
      (late_history_info bounds secondWaitExecution trace actual execution current).trans late.symm
    have chosen : ((Profile.update (sig := (nativeModel bounds).behavioralSignature)
        sourceProfile owner ((sourceProfile owner).withLaw site.1
          (retainedComparator bounds covers owner site))) owner
        (some (execution.recall owner, execution.observe app owner))).map Subtype.val =
          PMF.pure (some (lateResponse firstCandidate false)) := by
      rw [observed, Profile.update_same, InformationModel.BehavioralPolicy.withLaw_self]
      exact retainedComparator_second_wait bounds covers site late
    rw [late_native_response_value (nativeMenu bounds) _ history.1 execution current position
      (lateResponse firstCandidate false) chosen
      (fun state => auditedUtility sample deposit state owner),
      late_continuation_value execution firstCandidate
        ((nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler
          (current ▸ history.1.trace)) position ready entered clock empty sample authentic
            deposit false]
    apply effective_late_continuation_le_zero bounds targetProfile _ execution _ position ready
      entered clock sample deposit nonnegative
    exact ((bounds.riskMenu_in_effective (runtime setup) leaks bound).history_state
      (initialLaw setup) horizon scheduler history.1).trans current
  · let actual : (nativeModel bounds).InformationHistory owner
        (some ((secondDecisionExecution disclose).recall owner,
          (secondDecisionExecution disclose).observe app owner)) :=
      ⟨history.1, history.2.trans completed⟩
    have current : history.1.state = some ⟨4, some owner, secondDecisionExecution disclose⟩ :=
      second_decision_information_state bounds disclose actual
    rw [completed_risk_continuation_value bounds _ history.1 disclose current sample authentic
      deposit]
    apply completed_native_value_le (effectiveMenu bounds) targetProfile _ disclose _ sample
      deposit nonnegative
    exact ((bounds.riskMenu_in_effective (runtime setup) leaks bound).history_state
      (initialLaw setup) horizon scheduler history.1).trans current

/-- Any audited risk-menu equilibrium extends to an actual equilibrium of all
bounded effective responses. The complete terminal control law is preserved,
so every same-draw typed readout and audit settlement law is preserved too. -/
theorem risk_equilibrium_extends_effective (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (source : (nativeModel bounds).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium
      ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
      (nativeCertificate bounds) (fun who final => auditedUtility sample deposit final.state who)) :
    ∃ target : (effectiveModel bounds).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((effectiveMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (effectiveCertificate bounds)
        (fun who final => auditedUtility sample deposit final.state who) ∧
      (effectiveRestriction bounds).ExtendsProfile source.strategy target.strategy ∧
      (((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds) source.strategy
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
          ExecutionProtocol.History.state) =
        (((effectiveModel bounds).runBehavioralTerminalFrom (effectiveCertificate bounds)
          target.strategy
          ((effectiveMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
            ExecutionProtocol.History.state) := by
  classical
  obtain ⟨target, targetSE, agrees, _beliefs, histories, _payoffs⟩ :=
    (effectiveRestriction bounds).sequentialEquilibrium_extends_of_continuation
      ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
      (nativeCertificate bounds) (effectiveCertificate bounds)
      ((effectiveMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler)
      ((effectiveMenu bounds).uniform_fullyMixed (initialLaw setup) horizon scheduler)
      ((effectiveMenu bounds).decisionRecall (initialLaw setup) horizon scheduler)
      (retainedNativeDepth bounds)
      (retained_native_common_depth bounds (effectiveMenu bounds)
        (bounds.riskMenu_in_effective (runtime setup) leaks bound))
      (fun who final => auditedUtility sample deposit final.state who)
      (fun who final => auditedUtility sample deposit final.state who)
      (effective_embedded_audited_value bounds sample deposit)
      (by
        intro sourceProfile targetProfile _ who site action _ belief
        refine ⟨(sourceProfile who).withLaw site.1 (retainedComparator bounds covers who site), ?_⟩
        apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
        intro history _
        rw [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
            (effectiveModel bounds) (effectiveCertificate bounds)
            ((effectiveMenu bounds).bounded (initialLaw setup) horizon scheduler),
          InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
            (nativeModel bounds) (nativeCertificate bounds)
            ((nativeMenu bounds).bounded (initialLaw setup) horizon scheduler)]
        exact effective_whole_continuation_comparison bounds covers sample authentic deposit
          nonnegative sourceProfile _ who site history)
      source equilibrium
  refine ⟨target, targetSE, agrees, ?_⟩
  calc
    _ = (((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds) source.strategy
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
          (fun history => ((effectiveRestriction bounds).history history).state)) := by
      apply map_congr_on_support _
      intro history _
      exact ((bounds.riskMenu_in_effective (runtime setup) leaks bound).history_state
        (initialLaw setup) horizon scheduler history).symm
    _ = ((((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds) source.strategy
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
          (effectiveRestriction bounds).history).map ExecutionProtocol.History.state) :=
      (PMF.map_comp _ _ _).symm
    _ = _ := congrArg (PMF.map ExecutionProtocol.History.state) histories

end Vegas.LateResolutionService
