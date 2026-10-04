/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionFreeEquilibrium

/-! # Preservation of every source equilibrium in the native risk menu

The deterministic source prefix reaches one strategic input. Rationality forces
TRUE there; the checked free native risk-menu completion has the same joint
typed outcome and actual settlement. Full effective/raw extension is separate.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

private def sourcePrefixPosition (position : Fin 4) : setup.ProtocolState :=
  match position.val with
  | 0 => SourcePosition.root.state
  | 1 => SourcePosition.initialized.state
  | 2 => SourcePosition.sampled.state
  | _ => SourcePosition.ready.state

private theorem source_prefix_transition (position : Fin 3)
    (joint : Player → Option (OwnAction Player simpleExpr)) :
    setup.protocolStep (sourcePrefixPosition ⟨position.val, by omega⟩) joint =
      PMF.pure (sourcePrefixPosition ⟨position.val + 1, by omega⟩) := by
  fin_cases position
  · simp only [sourcePrefixPosition, SourcePosition.state, Setup.protocolStep,
      show setup.initialLaw = PMF.pure sourceInitial from rfl, PMF.pure_map]
    rfl
  · simp [sourcePrefixPosition, SourcePosition.state, Setup.protocolStep, setup, program,
      ProtocolState.step, ProtocolState.entry, sourceSampled, IExpr.evalDist, simpleExpr,
      evalLawDistExpr, RationalLaw.denote_pure, PMF.pure_map]
  · simp [sourcePrefixPosition, SourcePosition.state, Setup.protocolStep, setup, program,
      ProtocolState.step, ProtocolState.entry, sourceReady, IExpr.evalDist, simpleExpr,
      evalLawDistExpr, RationalLaw.denote_pure, PMF.pure_map]

private theorem source_prefix_state_step (profile : Profile sourceModel.behavioralSignature)
    (position : Fin 3) :
    setup.behavioralStateStep sourceAdmission profile
      (sourcePrefixPosition ⟨position.val, by omega⟩) =
      PMF.pure (sourcePrefixPosition ⟨position.val + 1, by omega⟩) := by
  classical
  have running : ¬ (sourcePrefixPosition ⟨position.val, by omega⟩).elim False
      (ProtocolState.terminal setup.program) := by fin_cases position <;> exact id
  unfold Setup.behavioralStateStep
  rw [ite_eq_right running]
  calc
    _ = (independentProduct fun who => profile who
        (setup.protocolObserve who (sourcePrefixPosition ⟨position.val, by omega⟩))).bind
          (fun _ => PMF.pure (sourcePrefixPosition ⟨position.val + 1, by omega⟩)) := by
      apply bind_congr_on_support _
      intro choices _
      exact source_prefix_transition position _
    _ = _ := PMF.bind_const _ _

/-- The actual original source input is reached under every behavioral profile. -/
theorem source_ready_prefix_law (profile : Profile sourceModel.behavioralSignature) :
    (sourceModel.runBehavioral profile 3).map ExecutionProtocol.History.state =
      PMF.pure SourcePosition.ready.state := by
  rw [InformationModel.runBehavioral, setup.runBehavioralFrom_state sourceAdmission]
  change (((PMF.pure SourcePosition.root.state).bind
    (setup.behavioralStateStep sourceAdmission profile)).bind
      (setup.behavioralStateStep sourceAdmission profile)).bind
        (setup.behavioralStateStep sourceAdmission profile) = _
  have first := source_prefix_state_step profile ⟨0, by decide⟩
  have second := source_prefix_state_step profile ⟨1, by decide⟩
  have third := source_prefix_state_step profile ⟨2, by decide⟩
  change setup.behavioralStateStep sourceAdmission profile SourcePosition.root.state =
    PMF.pure SourcePosition.initialized.state at first
  change setup.behavioralStateStep sourceAdmission profile SourcePosition.initialized.state =
    PMF.pure SourcePosition.sampled.state at second
  change setup.behavioralStateStep sourceAdmission profile SourcePosition.sampled.state =
    PMF.pure SourcePosition.ready.state at third
  rw [PMF.pure_bind, first, PMF.pure_bind, second, PMF.pure_bind, third]

private def sourceDecisionInfo : sourceModel.InfoState owner :=
  setup.protocolObserve owner SourcePosition.ready.state

private theorem source_ready_decision_info : sourceModel.IsDecisionInfo owner sourceDecisionInfo :=
    by
  obtain ⟨history, supported⟩ := (sourceModel.runBehavioral uniformSourceProfile 3).support_nonempty
  have actual : history.state ∈
      ((sourceModel.runBehavioral uniformSourceProfile 3).map
        ExecutionProtocol.History.state).support := by
    rw [PMF.support_map]
    exact Set.mem_image_of_mem _ supported
  rw [source_ready_prefix_law] at actual
  have current := (PMF.mem_support_pure_iff _ _).mp actual
  refine ⟨⟨history, ?_⟩, ?_, .reveal owner 0 true, ?_⟩
  · have observed : sourceModel.infoOf owner history.trace =
        setup.protocolObserve owner history.state :=
      setup.protocol_info sourceAdmission owner history.trace
    exact observed.trans (congrArg (setup.protocolObserve owner) current)
  · rw [current]
    exact id
  · change setup.protocolMenu sourceAdmission owner sourceDecisionInfo
      (some (.reveal owner 0 true))
    simp [sourceDecisionInfo, Setup.protocolMenu, Setup.protocolObserve, SourcePosition.state,
      setup, program, ProtocolState.observe, ProtocolView.menu, ProtocolView.actor,
      ProtocolView.available, owner]

private def sourceDecisionSite : sourceModel.InformationSite owner :=
  ⟨sourceDecisionInfo, source_ready_decision_info⟩

private def sourceDecisionLaw (profile : Profile sourceModel.behavioralSignature) : PMF Bool :=
  (profile owner sourceDecisionInfo).map (fun choice => OwnAction.disclosure choice.val)

private theorem source_ready_step_law (profile : Profile sourceModel.behavioralSignature)
    (site : sourceModel.InformationSite owner)
    (history : sourceModel.InformationHistory owner site.1) :
    (sourceModel.runBehavioralFrom profile 1 history.1).map ExecutionProtocol.History.state =
      (sourceDecisionLaw profile).map (fun disclose => SourcePosition.done disclose |>.state) := by
  have current := source_active_state owner site history
  have running : ¬ sourceArena.terminal history.1.state := by rw [current]; exact id
  rw [setup.run_one_choice_state sourceAdmission profile history.1 owner running
    (InformationModel.InformationSite.active sourceModel site history)]
  have observed : sourceModel.infoOf owner history.1.trace = sourceDecisionInfo := by
    have exactView : sourceModel.infoOf owner history.1.trace =
        setup.protocolObserve owner history.1.state :=
      setup.protocol_info sourceAdmission owner history.1.trace
    exact exactView.trans (congrArg (setup.protocolObserve owner) current)
  unfold sourceDecisionLaw
  rw [observed, PMF.map_comp]
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro choice _
  rw [current]
  simp [Setup.protocolStep, SourcePosition.state, setup, program,
    ProtocolState.step, ProtocolState.entry, sourceDone, PMF.pure_map]

private theorem source_context_decision_value
    (assessment : sourceModel.BehavioralAssessment) :
    (assessment.truncatedContinuationContext sourceDecisionSite (sourcePayoff owner) 1).value
      (assessment.strategy owner) =
        expect (sourceDecisionLaw assessment.strategy)
          (fun disclose => if disclose then 1 else 0) :=
    by
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    Profile.update_eq_self, expect_bind_of_finite]
  calc
    _ = expect (assessment.belief owner sourceDecisionSite) (fun _ =>
        expect (sourceDecisionLaw assessment.strategy)
          (fun disclose => if disclose then (1 : ℝ) else 0)) := by
      apply expect_congr_on_support
      intro history _
      let payoff (state : setup.ProtocolState) :=
        (setup.protocolReadout state).elim 0 (fun source => sourceUtility source owner)
      calc
        _ = expect ((sourceModel.runBehavioralFrom assessment.strategy 1 history.1).map
            ExecutionProtocol.History.state) payoff := (expect_map _ _ _).symm
        _ = _ := by
          rw [source_ready_step_law assessment.strategy sourceDecisionSite history, expect_map]
          apply expect_congr_on_support
          intro disclose _
          exact source_done_payoff owner disclose
    _ = _ := expect_constant _ _

/-- Source sequential rationality forces the actual disclosure law to TRUE. -/
private theorem source_equilibrium_decision_true (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium (setup.decision_antichain sourceAdmission)
      sourceCertificate sourcePayoff) : sourceDecisionLaw source.strategy = PMF.pure true := by
  have rational := ((source.isSequentialEquilibrium_iff_truncated_of_bounded sourceModel
    (setup.decision_antichain sourceAdmission) sourceCertificate
    (setup.protocol_bounded sourceAdmission) sourcePayoff).mp equilibrium).1
  have context := source.truncatedContinuationContext_remaining sourceModel 4
    (setup.protocol_bounded sourceAdmission) owner sourceDecisionSite 3
    (source_site_depth owner sourceDecisionSite) (sourcePayoff owner)
  change source.truncatedContinuationContext sourceDecisionSite (sourcePayoff owner) 1 = _
    at context
  have optimal := rational owner sourceDecisionSite
  change Context.IsLocallyOptimal
    (source.truncatedContinuationContext sourceDecisionSite (sourcePayoff owner) 4)
    Set.univ (source.strategy owner) at optimal
  rw [← context] at optimal
  have deviation := (Context.isLocallyOptimal_iff_of_integrable
    (payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)).mp optimal
      (sourceProfile (PMF.pure true) owner) (Set.mem_univ _)
  have allOwners : Profile.update (sig := sourceModel.behavioralSignature) source.strategy owner
      (sourceProfile (PMF.pure true) owner) = sourceProfile (PMF.pure true) := by
    funext who
    have same : who = owner := Subsingleton.elim _ _
    subst who
    rw [Profile.update_same]
  have opening :
      (source.truncatedContinuationContext sourceDecisionSite (sourcePayoff owner) 1).value
      (sourceProfile (PMF.pure true) owner) = 1 := by
    rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value, allOwners,
      expect_bind_of_finite]
    calc
      _ = expect (source.belief owner sourceDecisionSite) (fun _ => (1 : ℝ)) := by
        apply expect_congr_on_support
        intro history _
        exact source_opening_value owner sourceDecisionSite history
      _ = _ := expect_constant _ _
  rw [opening, source_context_decision_value] at deviation
  have mass : (sourceDecisionLaw source.strategy true).toReal = 1 := by
    have identity : expect (sourceDecisionLaw source.strategy)
        (fun disclose => if disclose then (1 : ℝ) else 0) =
        (sourceDecisionLaw source.strategy true).toReal := by
      simpa only [eq_comm, mul_one] using
        expect_ite_eq (sourceDecisionLaw source.strategy) true 1
    rw [identity] at deviation
    exact le_antisymm (pmf_toReal_apply_le_one _ _) deviation
  have full : (sourceDecisionLaw source.strategy) true = 1 := by
    calc
      _ = ENNReal.ofReal ((sourceDecisionLaw source.strategy true).toReal) :=
        (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm
      _ = _ := by rw [mass, ENNReal.ofReal_one]
  have unique := (PMF.apply_eq_one_iff _ _).mp full
  calc
    _ = (sourceDecisionLaw source.strategy).map (fun _ => true) := by
      have retained : (sourceDecisionLaw source.strategy).map id =
          (sourceDecisionLaw source.strategy).map (fun _ => true) := by
        apply map_congr_on_support _
        intro value supported
        exact Set.mem_singleton_iff.mp (unique ▸ supported)
      simpa only [PMF.map_id] using retained
    _ = _ := PMF.map_const _ _

private theorem source_profile_readout_law (profile : Profile sourceModel.behavioralSignature) :
    (sourceModel.runBehavioral profile 4).map (fun final => setup.protocolReadout final.state) =
      (sourceDecisionLaw profile).map (fun disclose => some (sourceDone disclose).state) := by
  change (sourceModel.runBehavioralFrom profile 4 sourceArena.initHistory).map
    (fun final => setup.protocolReadout final.state) = _
  rw [show 4 = 3 + 1 by decide, InformationModel.runBehavioralFrom_add, PMF.map_bind]
  calc
    _ = (sourceModel.runBehavioralFrom profile 3 sourceArena.initHistory).bind
        (fun _ => (sourceDecisionLaw profile).map
          (fun disclose => some (sourceDone disclose).state)) := by
      apply bind_congr_on_support _
      intro history supported
      have actual : history.state ∈ ((sourceModel.runBehavioral profile 3).map
          ExecutionProtocol.History.state).support := by
        rw [PMF.support_map]
        exact Set.mem_image_of_mem _ supported
      rw [source_ready_prefix_law] at actual
      have current := (PMF.mem_support_pure_iff _ _).mp actual
      let information : sourceModel.InformationHistory owner sourceDecisionSite.1 :=
        ⟨history, by
          have viewEq : sourceModel.infoOf owner history.trace =
              setup.protocolObserve owner history.state :=
            setup.protocol_info sourceAdmission owner history.trace
          exact viewEq.trans (congrArg (setup.protocolObserve owner) current)⟩
      calc
        _ = ((sourceModel.runBehavioralFrom profile 1 history).map
            ExecutionProtocol.History.state).map setup.protocolReadout :=
          (PMF.map_comp _ _ _).symm
        _ = _ := by
          rw [source_ready_step_law profile sourceDecisionSite information, PMF.map_comp]
          rfl
    _ = _ := PMF.bind_const _ _

/-- Every source equilibrium has the same actual typed TRUE terminal law. -/
theorem source_equilibrium_joint_law (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium (setup.decision_antichain sourceAdmission)
      sourceCertificate sourcePayoff) :
    (sourceModel.runBehavioralTerminalFrom sourceCertificate source.strategy
      sourceArena.initHistory).map
        (fun final => (setup.protocolReadout final.state, fun who => sourcePayoff who final)) =
      PMF.pure (some (sourceDone true).state,
        fun who => sourceUtility (sourceDone true).state who) := by
  have actual : (sourceModel.runBehavioral source.strategy 4).map
      (fun final => setup.protocolReadout final.state) =
        PMF.pure (some (sourceDone true).state) := by
    rw [source_profile_readout_law, source_equilibrium_decision_true source equilibrium,
      PMF.pure_map]
  rw [InformationModel.runBehavioralTerminalFrom_initHistory sourceModel sourceCertificate
    source.strategy (setup.protocol_bounded sourceAdmission)]
  calc
    _ = ((sourceModel.runBehavioral source.strategy 4).map
        (fun final => setup.protocolReadout final.state)).map
          (fun state => (state,
            fun who => state.elim 0 (fun value => sourceUtility value who))) :=
      (PMF.map_comp _ _ _).symm
    _ = _ := by rw [actual, PMF.pure_map]; rfl

/-- Each original source SE is preserved by an actual native risk-menu SE for
this service, including the joint typed outcome and actual audit settlement.
The late site is completed rationally with FALSE; no source assessment or
native posterior equation is supplied. Full effective/raw extension is separate. -/
theorem every_source_equilibrium_preserved_in_risk_menu (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium (setup.decision_antichain sourceAdmission)
      sourceCertificate sourcePayoff) :
    ∃ native : (nativeModel bounds).BehavioralAssessment,
      native.strategy = freeNativeProfile bounds covers ∧
      native.IsSequentialEquilibrium
        ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (nativeCertificate bounds)
        (fun who final => auditedUtility sample deposit final.state who) ∧
      (sourceModel.runBehavioralTerminalFrom sourceCertificate source.strategy
        sourceArena.initHistory).map
          (fun final => (setup.protocolReadout final.state, fun who => sourcePayoff who final)) =
      ((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds) native.strategy
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).bind
          (fun final =>
            (GameTheory.Enforcement.TerminalAudit.settlement
              (baseUtility setup leaks sourceUtility)
              ((runtime setup).serviceAuditObservation leaks)
              (sourceServiceAudit setup leaks sample) (fun _ => deposit) final.state).map
                (fun payoffs => (sourceReadout setup leaks final.state, payoffs))) := by
  obtain ⟨native, strategy, nativeEquilibrium⟩ :=
    exists_free_native_equilibrium bounds covers sample authentic deposit nonnegative
  refine ⟨native, strategy, nativeEquilibrium, ?_⟩
  rw [source_equilibrium_joint_law source equilibrium, strategy,
    freeNativeProfile_readout_settlement bounds covers sample authentic deposit]

end Vegas.LateResolutionService
