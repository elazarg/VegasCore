/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionNativeSites
import Vegas.Examples.LateResolutionFirstOptimality

/-! # A source-preserving rational completion in the native risk menu -/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

theorem second_wait_ready : secondWaitExecution.application.config.cut.Ready resolution := by
  decide

theorem second_wait_clock : secondWaitExecution.application.clock = 1 := rfl

theorem second_wait_entered : secondWaitExecution.application.activatedAt resolution = some 0 :=
  rfl

theorem second_wait_empty : secondWaitExecution.network = .empty := rfl

theorem second_wait_withhold_available (bounds : MessageBounds nativeGraph) :
    lateResponse firstCandidate false ∈ (nativeMenu bounds).actions owner
      (secondWaitExecution.recall owner) (secondWaitExecution.observe app owner) := by
  have turn : (secondWaitExecution.observe app owner).application.publicView.ownTurn? owner =
      some resolution := ownTurn?_of_ready setup _ second_wait_ready resolution_actor
  have risky : (runtime setup).serviceRisk leaks bound owner
      (secondWaitExecution.recall owner) (secondWaitExecution.observe app owner) = true := by
    apply (runtime setup).serviceRisk_of_opportunity
    apply ((runtime setup).firstUnprotectedOpportunity_iff leaks bound owner _ _).mpr
    refine ⟨rfl, resolution, turn, rfl, ?_⟩
    change ¬ (1 - 0 + 2 < 3)
    decide
  change lateResponse firstCandidate false ∈ bounds.riskActions (runtime setup) leaks bound owner
    _ _
  rw [bounds.riskActions_of_risk _ _ _ _ _ _ risky, bounds.menu_mem]
  refine ⟨⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
  simp only [lateResponse, Bool.false_eq_true, ↓reduceIte,
    ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
    disclosureSubmission, EvidenceRequest.normalize_none]

open Classical in
def freeNativeProfile (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values) :
    ∀ who, (nativeModel bounds).BehavioralPolicy who :=
  let reference := ((nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler)
  let early := some (firstExecution.recall owner, firstExecution.observe app owner)
  let late := some (secondWaitExecution.recall owner, secondWaitExecution.observe app owner)
  let earlyChoice : (nativeModel bounds).Choice owner early :=
    ⟨some (lateResponse firstCandidate true), lateResponse firstCandidate true,
      first_response_available bounds covers true, rfl⟩
  let lateChoice : (nativeModel bounds).Choice owner late :=
    ⟨some (lateResponse firstCandidate false), lateResponse firstCandidate false,
      second_wait_withhold_available bounds, rfl⟩
  Profile.update (sig := (nativeModel bounds).behavioralSignature) reference.strategy owner
    (((reference.strategy owner).withLaw early (PMF.pure earlyChoice)).withLaw late
      (PMF.pure lateChoice))

theorem first_info_ne_second_wait :
    some (firstExecution.recall owner, firstExecution.observe app owner) ≠
      some (secondWaitExecution.recall owner, secondWaitExecution.observe app owner) := by
  intro equal
  have length := congrArg (fun info : app.Info => info.map (fun input => input.1.length)) equal
  change some 0 = some 1 at length
  cases length

theorem freeNativeProfile_first (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values) :
    (freeNativeProfile bounds covers owner (firstSite bounds).1).map Subtype.val =
      PMF.pure (some (lateResponse firstCandidate true)) := by
  classical
  simp only [firstSite, freeNativeProfile, Profile.update_same]
  rw [InformationModel.BehavioralPolicy.withLaw_of_ne (M := nativeModel bounds) (i := owner)
      _ _ _ first_info_ne_second_wait, InformationModel.BehavioralPolicy.withLaw_self,
    PMF.pure_map]

theorem freeNativeProfile_second_wait (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values) :
    (freeNativeProfile bounds covers owner
      (some (secondWaitExecution.recall owner, secondWaitExecution.observe app owner))).map
        Subtype.val = PMF.pure (some (lateResponse firstCandidate false)) := by
  classical
  simp only [freeNativeProfile, Profile.update_same,
    InformationModel.BehavioralPolicy.withLaw_self, PMF.pure_map]

/-- An actual site with the silent first recall has the concrete late state. -/
theorem second_wait_site_trace (bounds : MessageBounds nativeGraph)
    (site : (nativeModel bounds).InformationSite owner)
    (atSite : site.1 = some (secondWaitExecution.recall owner,
      secondWaitExecution.observe app owner)) :
    Nonempty (((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, secondWaitExecution⟩)) := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active (nativeModel bounds) site history
  cases current : history.1.state with
  | none => rw [current] at active; cases active
  | some control =>
      rw [current] at active
      have observed := ((nativeMenu bounds).info (initialLaw setup) horizon scheduler owner
        history.1.trace).symm.trans (history.2.trans atSite)
      rcases native_decision_history_cases bounds history.1 control current active with
        first | late | ⟨disclose, complete⟩
      · rw [first] at observed
        have same := congrArg (fun info : app.Info => info.map (fun input => input.1.length))
          observed
        change some 0 = some 1 at same
        cases same
      · exact ⟨late ▸ history.1.trace⟩
      · rw [complete] at observed
        have same := congrArg (fun info : app.Info => info.map
          (fun input => input.1.map (fun entry => entry.action.transmission.isSome))) observed
        cases disclose <;> change some [true] = some [false] at same <;> cases same

theorem freeNativeProfile_rational (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (assessment : (nativeModel bounds).BehavioralAssessment)
    (strategy : assessment.strategy = freeNativeProfile bounds covers) :
    assessment.IsSequentiallyRationalFor (fun who site =>
      assessment.truncatedContinuationContext site
        (fun final => auditedUtility sample deposit final.state who) 21) := by
  intro who site
  have own : who = owner := Subsingleton.elim _ _
  subst who
  rcases native_decision_site_cases bounds site with first | late | ⟨disclose, complete⟩
  · have same : site = firstSite bounds := Subtype.ext first
    subst site
    apply first_opening_locally_optimal bounds sample authentic deposit nonnegative assessment
    rw [strategy]
    exact freeNativeProfile_first bounds covers
  · obtain ⟨trace⟩ := second_wait_site_trace bounds site late
    have same : site = lateSite bounds secondWaitExecution trace := Subtype.ext late
    subst site
    apply late_false_locally_optimal bounds secondWaitExecution trace second_wait_ready
      second_wait_entered second_wait_clock second_wait_empty sample authentic deposit nonnegative
        assessment firstCandidate
    rw [strategy]
    exact freeNativeProfile_second_wait bounds covers
  · exact second_decision_locally_optimal bounds disclose site complete assessment
      (fun state => auditedUtility sample deposit state owner)

/-- The native risk menu admits a rational completion which retains the first
opening. Consistency is constructed from native fully mixed assessments. -/
theorem exists_free_native_equilibrium (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) :
    ∃ assessment : (nativeModel bounds).BehavioralAssessment,
      assessment.strategy = freeNativeProfile bounds covers ∧
      assessment.IsSequentialEquilibrium
        ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (nativeCertificate bounds)
        (fun who final => auditedUtility sample deposit final.state who) := by
  obtain ⟨assessment, strategy, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion
      ((nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler)
      ((nativeMenu bounds).uniform_fullyMixed (initialLaw setup) horizon scheduler)
      ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
      (freeNativeProfile bounds covers)
  refine ⟨assessment, strategy, ?_⟩
  apply (assessment.isSequentialEquilibrium_iff_truncated_of_bounded (nativeModel bounds)
    ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
    (nativeCertificate bounds) ((nativeMenu bounds).bounded (initialLaw setup) horizon scheduler)
    (fun who final => auditedUtility sample deposit final.state who)).mpr
  exact ⟨freeNativeProfile_rational bounds covers sample authentic deposit nonnegative assessment
    strategy, consistent⟩

/-- The completed native play still realizes the protected source opening. -/
theorem freeNativeProfile_run_state (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values) :
    ((nativeModel bounds).runBehavioral (freeNativeProfile bounds covers) 21).map
      ExecutionProtocol.History.state =
        PMF.pure (app.finished (firstDecisionEndpoint true)) := by
  change ((nativeModel bounds).runBehavioralFrom (freeNativeProfile bounds covers) 21
    ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
      ExecutionProtocol.History.state = _
  rw [show 21 = 4 + 17 by decide, InformationModel.runBehavioralFrom_add, PMF.map_bind]
  calc
    _ = ((nativeModel bounds).runBehavioralFrom (freeNativeProfile bounds covers) 4
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).bind
          (fun _ => PMF.pure (app.finished (firstDecisionEndpoint true))) := by
      apply bind_congr_on_support _
      intro history supported
      have actual : history.state ∈
          (((nativeModel bounds).runBehavioral (freeNativeProfile bounds covers) 4).map
            ExecutionProtocol.History.state).support := by
        rw [PMF.support_map]
        exact Set.mem_image_of_mem _ supported
      rw [first_native_prefix] at actual
      exact first_native_decided_run bounds (freeNativeProfile bounds covers) history
        ((PMF.mem_support_pure_iff _ _).mp actual) true
        (freeNativeProfile_first bounds covers) 17 (by decide)
    _ = _ := PMF.bind_const _ _

theorem freeNativeProfile_terminal_state (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values) :
    ((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds)
      (freeNativeProfile bounds covers)
      ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
        ExecutionProtocol.History.state =
          PMF.pure (app.finished (firstDecisionEndpoint true)) := by
  rw [InformationModel.runBehavioralTerminalFrom_initHistory (nativeModel bounds)
    (nativeCertificate bounds) (freeNativeProfile bounds covers)
    ((nativeMenu bounds).bounded (initialLaw setup) horizon scheduler)]
  exact freeNativeProfile_run_state bounds covers

/-- The same actual audit draw preserves the typed source readout and the full
realized payoff vector. Authentic partial observation suffices on this play. -/
theorem freeNativeProfile_readout_settlement (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) :
    ((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds)
      (freeNativeProfile bounds covers)
      ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).bind
        (fun final =>
          (GameTheory.Enforcement.TerminalAudit.settlement (baseUtility setup leaks sourceUtility)
            ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
            (fun _ => deposit) final.state).map
              (fun payoffs => (sourceReadout setup leaks final.state, payoffs))) =
      PMF.pure (some (sourceDone true).state,
        fun who => sourceUtility (sourceDone true).state who) := by
  let settle (state : app.ProtocolState) :=
    (GameTheory.Enforcement.TerminalAudit.settlement (baseUtility setup leaks sourceUtility)
      ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      (fun _ => deposit) state).map (fun payoffs => (sourceReadout setup leaks state, payoffs))
  change ((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds)
    (freeNativeProfile bounds covers)
    ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).bind
      (fun final => settle final.state) = _
  rw [show ((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds)
      (freeNativeProfile bounds covers)
      ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).bind
        (fun final => settle final.state) =
      (((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds)
        (freeNativeProfile bounds covers)
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
          ExecutionProtocol.History.state).bind settle from
    (PMF.bind_map
      ((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds)
        (freeNativeProfile bounds covers)
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory)
      (fun final : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History =>
        final.state) settle).symm]
  rw [freeNativeProfile_terminal_state, PMF.pure_bind]
  have clean : ∀ who, GameTheory.Enforcement.TerminalAudit.charge
      ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      (app.finished (firstDecisionEndpoint true)) who = 0 := by
    intro who
    have same : who = owner := Subsingleton.elim _ _
    subst who
    exact first_endpoint_charge true sample authentic
  dsimp only [settle]
  rw [GameTheory.Enforcement.TerminalAudit.settlement_clean _ _ _ _ _ clean, PMF.pure_map,
    first_endpoint_readout]
  have baseEq : baseUtility setup leaks sourceUtility (app.finished (firstDecisionEndpoint true)) =
      (fun who => sourceUtility (sourceDone true).state who) := by
    funext who
    unfold baseUtility
    rw [first_endpoint_readout]
    rfl
  rw [baseEq]

theorem source_opening_readout :
    (sourceModel.runBehavioral (sourceProfile (PMF.pure true)) 4).map
      (fun final => setup.protocolReadout final.state) =
        PMF.pure (some (sourceDone true).state) := by
  have law := setup.protocol_runBehavioral_eq sourceAdmission
    (fun who => sourcePolicy (PMF.pure true) who) (sourcePolicy_admitted (PMF.pure true))
  rw [(setup.informationModel sourceAdmission).runSingleMoverBehavioralFrom_eq_runBehavioralFrom]
    at law
  change (sourceModel.runBehavioral (sourceProfile (PMF.pure true)) 4).map
    (fun final => setup.protocolReadout final.state) = _ at law
  rw [law]
  have evaluated : setup.run (fun who => sourcePolicy (PMF.pure true) who) =
      PMF.pure (sourceDone true).state := by
    rw [Setup.run, show setup.initialLaw = PMF.pure sourceInitial from rfl, PMF.pure_bind]
    change SourceProgram.run program (fun who => sourcePolicy (PMF.pure true) who)
      sourceInitial = _
    simp only [SourceProgram.run, program, runWith, IExpr.evalDist, simpleExpr,
      evalLawDistExpr, RationalLaw.denote_pure, sourcePolicy, afterSample, revealKernel,
      PMF.pure_bind]
    rfl
  rw [evaluated, PMF.pure_map]

theorem source_opening_joint_law :
    (sourceModel.runBehavioralTerminalFrom sourceCertificate (sourceProfile (PMF.pure true))
      sourceArena.initHistory).map
        (fun final => (setup.protocolReadout final.state, fun who => sourcePayoff who final)) =
      PMF.pure (some (sourceDone true).state,
        fun who => sourceUtility (sourceDone true).state who) := by
  rw [InformationModel.runBehavioralTerminalFrom_initHistory sourceModel sourceCertificate
    (sourceProfile (PMF.pure true)) (setup.protocol_bounded sourceAdmission)]
  calc
    _ = ((sourceModel.runBehavioral (sourceProfile (PMF.pure true)) 4).map
        (fun final => setup.protocolReadout final.state)).map
          (fun source => (source,
            fun who => source.elim 0 (fun value => sourceUtility value who))) :=
      (PMF.map_comp _ _ _).symm
    _ = _ := by rw [source_opening_readout, PMF.pure_map]; rfl

/-- This fixture has source and native risk-menu sequential equilibria with the same
joint typed readout and actual terminal settlement vector. The raw completion
chooses FALSE at the unrecorded late site and TRUE at the protected first site.
This statement uses `nativeMenu = bounds.riskMenu`, with raw choices at risky
sites; extension to the full effective and raw protocols is separate. -/
theorem exists_source_preserving_native_equilibrium (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) :
    ∃ source : sourceModel.BehavioralAssessment,
      ∃ native : (nativeModel bounds).BehavioralAssessment,
        source.strategy = sourceProfile (PMF.pure true) ∧
        source.IsSequentialEquilibrium (setup.decision_antichain sourceAdmission)
          sourceCertificate sourcePayoff ∧
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
  obtain ⟨source, sourceStrategy, sourceEquilibrium⟩ := exists_source_opening_equilibrium
  obtain ⟨native, nativeStrategy, nativeEquilibrium⟩ :=
    exists_free_native_equilibrium bounds covers sample authentic deposit nonnegative
  refine ⟨source, native, sourceStrategy, sourceEquilibrium, nativeStrategy, nativeEquilibrium, ?_⟩
  rw [sourceStrategy, nativeStrategy, source_opening_joint_law,
    freeNativeProfile_readout_settlement bounds covers sample authentic deposit]

end Vegas.LateResolutionService
