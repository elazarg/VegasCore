/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningIncentives
import VegasTests.SelectiveAssociationOpeningSelection
import VegasTests.SelectiveAssociationOpeningSettlement
import VegasTests.SelectiveAssociationPublication

/-! # Sequential rationality forces ordinary opening

The complete raw response menu is retained. For each fixed response, the
publication owner sees enough to determine the result of reserved inclusion
and timeout. A failure at even a zero-belief compatible history is therefore
a failure throughout that information set and is strictly suboptimal.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

def nativePublicationAt (who : Player) (state : nativeApp.ProtocolState) :
    Option (PublicationResult Bool) :=
  state.bind (fun control =>
    (nativePublicationRef who).get? control.execution.application.config.store)

open Classical in
theorem native_committed_response
    {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
    (profile : ∀ who, (serviceModel observation).BehavioralPolicy who) (who : Player)
    (info : (serviceModel observation).InfoState who)
    (choice : (serviceModel observation).Choice who info)
    (response : (serviceApp observation).Action) (selected : choice.1 = some response)
    (past : List (serviceApp observation).PlayerEntry) (view : (serviceApp observation).PlayerView)
    (information : some (past, view) = info) :
    (serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation)
      (Profile.update (sig := (serviceModel observation).behavioralSignature) profile who
        ((profile who).commit info choice)) who past view = FinDist.pure response := by
  simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, Profile.update_same]
  rw [information]
  simp only [InformationModel.BehavioralPolicy.commit_self, FinDist.map_pure]
  change FinDist.pure (choice.1.getD ⟨none⟩) = _
  rw [selected]
  rfl

theorem native_settlement_behavioral
    (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (who : Player) (response : nativeApp.Action) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉ control.execution.application.config.cut.completed)
    (chooses : nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
      profile who (control.execution.recall who) (control.execution.observe nativeApp who) =
        FinDist.pure response)
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    ∃ middle ∈ (nativeRuntime.interactionStep nativeLeaks
        (nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
          profile)
        nativeNetwork (.includeLatest (nativePublicationEvent who) who)
        (control.execution.respond nativeApp who response)).support,
      nativePublicationAt who final.state =
        some (((nativePublicationRef who).get? middle.application.config.store).getD .failure) := by
  have law := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    profile (2 * nativeHorizon + 1) ⟨some control, trace⟩ (by
      change nativeApp.rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1
      have bound := nativeApp.trace_bound (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
        (nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace)
      omega)
  obtain ⟨middle, middleMem, result, stateEq, published⟩ := native_response_settlement_finish
    _ control trace who response active granted unfinished chooses final.state (by
      rw [← law, FinDist.support_map]
      exact ⟨final, supported, rfl⟩)
  exact ⟨middle, middleMem, by
    simpa only [nativePublicationAt, stateEq, Option.bind_some] using published⟩

private theorem publication_site_facts (who : Player) (view : nativeApp.PlayerView)
    (control : nativeApp.Control) (observed : control.execution.observe nativeApp who = view)
    (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store =
      some (.success bit)) :
    control.execution.application.serviceGrant = some (nativePublicationEvent who) ∧
      nativePublicationEvent who ∉ control.execution.application.config.cut.completed ∧
      (nativeBindingRef who).get? control.execution.application.config.store =
        some (.success bit) := by
  rw [← observed] at granted unfinished stored
  refine ⟨granted, ?_, ?_⟩
  · change nativePublicationEvent who ∉
      control.execution.application.config.history.map EventGraph.Completion.event at unfinished
    exact fun completed => unfinished
      ((control.execution.application.config.history_exact _).mpr completed)
  · change (nativeBindingRef who).get?
      (nativeGraph.playerStore who control.execution.application.config.store) = _ at stored
    rwa [(nativeBindingRef who).get?_playerStore who _ rfl] at stored

open Classical in
/-- The final publication of one pure raw response is constant throughout the
owner's information set, even when the continuations of other players differ. -/
theorem native_committed_publication_local
    (profile : ∀ who, nativeModel.BehavioralPolicy who) (who : Player)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store = some (.success bit))
    (choice : nativeModel.Choice who (some (past, view)))
    (first second : nativeModel.InformationHistory who (some (past, view)))
    (firstFinal secondFinal : nativeArena.History)
    (firstMem : firstFinal ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) profile who
        ((profile who).commit (some (past, view)) choice)) (2 * nativeHorizon + 1) first.1).support)
    (secondMem : secondFinal ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) profile who
        ((profile who).commit (some (past, view)) choice))
          (2 * nativeHorizon + 1) second.1).support) :
    nativePublicationAt who firstFinal.state = nativePublicationAt who secondFinal.state := by
  obtain ⟨response, _, selected⟩ := choice.2
  obtain ⟨left, leftEq, leftActive, leftRecall, leftView⟩ :=
    native_information_control who past view first
  obtain ⟨right, rightEq, rightActive, rightRecall, rightView⟩ :=
    native_information_control who past view second
  rcases first with ⟨⟨leftState, leftTrace⟩, firstInfo⟩
  rcases second with ⟨⟨rightState, rightTrace⟩, secondInfo⟩
  change leftState = some left at leftEq
  change rightState = some right at rightEq
  subst leftState
  subst rightState
  let changed := Profile.update (sig := nativeModel.behavioralSignature) profile who
    ((profile who).commit (some (past, view)) choice)
  obtain ⟨leftGrant, leftUnfinished, leftStored⟩ :=
    publication_site_facts who view left leftView bit granted unfinished stored
  obtain ⟨rightGrant, rightUnfinished, _⟩ :=
    publication_site_facts who view right rightView bit granted unfinished stored
  obtain ⟨afterLeft, afterLeftMem, leftPublished⟩ := native_settlement_behavioral changed left
    leftTrace who response leftActive leftGrant leftUnfinished
    (native_committed_response profile who _ choice response selected _ _
      (congrArg some (Prod.ext leftRecall leftView))) firstFinal firstMem
  obtain ⟨afterRight, afterRightMem, rightPublished⟩ := native_settlement_behavioral changed right
    rightTrace who response rightActive rightGrant rightUnfinished
    (native_committed_response profile who _ choice response selected _ _
      (congrArg some (Prod.ext rightRecall rightView))) secondFinal secondMem
  have leftInput : (left.execution.recall who, left.execution.observe nativeApp who) =
      (past, view) := Prod.ext leftRecall leftView
  have rightInput : (right.execution.recall who, right.execution.observe nativeApp who) =
      (past, view) := Prod.ext rightRecall rightView
  have localView := native_opening_reserved_local left right leftTrace rightTrace who
    leftActive rightActive (leftInput.trans rightInput.symm)
    leftGrant bit leftStored response _ afterLeft afterRight afterLeftMem afterRightMem
  have same := native_publication_playerView_congr _ _ who localView
  rw [leftPublished, rightPublished, same]

open Classical in
theorem native_committed_publication_present
    (profile : ∀ who, nativeModel.BehavioralPolicy who) (who : Player)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store = some (.success bit))
    (choice : nativeModel.Choice who (some (past, view)))
    (history : nativeModel.InformationHistory who (some (past, view)))
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) profile who
        ((profile who).commit (some (past, view)) choice))
          (2 * nativeHorizon + 1) history.1).support) :
    ∃ publication, nativePublicationAt who final.state = some publication := by
  obtain ⟨response, _, selected⟩ := choice.2
  obtain ⟨control, stateEq, active, recall, observed⟩ :=
    native_information_control who past view history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  obtain ⟨grant, incomplete, _⟩ :=
    publication_site_facts who view control observed bit granted unfinished stored
  obtain ⟨_, _, published⟩ := native_settlement_behavioral _ control trace who response active
    grant incomplete (native_committed_response profile who _ choice response selected _ _
      (congrArg some (Prod.ext recall observed))) final supported
  exact ⟨_, published⟩

open Classical in
/-- Every supported raw response at a usable opening site succeeds under a
sequentially rational assessment, including at histories assigned zero belief. -/
theorem native_supported_opening_succeeds
    (assessment : nativeModel.BehavioralAssessment) (who : Player)
    (site : nativeModel.InformationSite who)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (siteEq : site.1 = some (past, view)) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store = some (.success bit))
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site (fun history => nativeUtility who history.state)
        (2 * nativeHorizon + 1)))
    (choice : nativeModel.Choice who site.1)
    (chosen : choice ∈ (assessment.strategy who site.1).support)
    (history : nativeModel.InformationHistory who site.1) (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).commit site.1 choice))
          (2 * nativeHorizon + 1) history.1).support) :
    ∃ publishedBit, nativePublicationAt who final.state = some (.success publishedBit) := by
  classical
  rcases site with ⟨info, isSite⟩
  change info = some (past, view) at siteEq
  subst info
  obtain ⟨publication, published⟩ := native_committed_publication_present assessment.strategy who
    past view bit granted unfinished stored choice history final supported
  cases publication with
  | success publishedBit => exact ⟨publishedBit, published⟩
  | failure =>
      exfalso
      apply (native_not_supported_failing_opening assessment who ⟨some (past, view), isSite⟩
        past view rfl bit granted unfinished stored rational choice _) chosen
      intro other otherFinal otherMem
      have same := native_committed_publication_local assessment.strategy who past view bit
        granted unfinished stored choice history other final otherFinal supported otherMem
      have failed : nativePublicationAt who otherFinal.state = some .failure :=
        same.symm.trans published
      cases stateEq : otherFinal.state with
      | none => simp only [nativePublicationAt, stateEq, Option.bind_none] at failed; cases failed
      | some control =>
          exact ⟨control, rfl, by
            simpa only [nativePublicationAt, stateEq, Option.bind_some] using failed⟩

open Classical in
/-- Under the assessment's complete strategy, each compatible opening history
also publishes successfully. This includes every branch of the current mixed
response and all subsequent behavior. -/
theorem native_sequentially_rational_opening_succeeds
    (assessment : nativeModel.BehavioralAssessment) (who : Player)
    (site : nativeModel.InformationSite who)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (siteEq : site.1 = some (past, view)) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store = some (.success bit))
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site (fun history => nativeUtility who history.state)
        (2 * nativeHorizon + 1)))
    (history : nativeModel.InformationHistory who site.1) (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom assessment.strategy
      (2 * nativeHorizon + 1) history.1).support) :
    ∃ publishedBit, nativePublicationAt who final.state = some (.success publishedBit) := by
  classical
  have once := nativeModel.actsOnceWhereItMatters_of_actsOnce
    (InformationModel.actsOnce_of_decisionInformationAntichain
      (nativeMenu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon
        nativeScheduler))
  have law := nativeModel.runBehavioralFrom_update_withLaw_eq_bind once assessment.strategy who
    (assessment.strategy who) site.1 (assessment.strategy who site.1) history.1 history.2
    (nativeMenu.informationSite_allNonterminal (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler who site history)
    (InformationModel.InformationSite.active nativeModel site history) (2 * nativeHorizon)
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self] at law
  rw [law] at supported
  obtain ⟨choice, chosen, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  exact native_supported_opening_succeeds assessment who site past view siteEq bit granted
    unfinished stored rational choice chosen history final finalMem

/-- A value already bound at any legal history is unchanged throughout every
behavioral continuation, independently of the assessment and future choices. -/
theorem native_binding_continuation
    (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (who : Player) (value : PublicationResult Bool)
    (stored : (nativeBindingRef who).get? control.execution.application.config.store = some value)
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    ∃ result, final.state = some result ∧
      (nativeBindingRef who).get? result.execution.application.config.store = some value := by
  let players := nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler profile
  have law := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    profile (2 * nativeHorizon + 1) ⟨some control, trace⟩ (by
      change nativeApp.rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1
      have bound := nativeApp.trace_bound (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
        (nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace)
      omega)
  have finished : final.state ∈ (nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler players (some control)).support := by
    rw [← law, FinDist.support_map]
    exact ⟨final, supported, rfl⟩
  simp only [ReactiveApplication.finish] at finished
  obtain ⟨execution, executionMem, stateEq⟩ := FinDist.support_map .. ▸ finished
  obtain ⟨middle, middleMem, executionMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ executionMem)
  have invariant := ReactiveApplication.Invariant.policyInvariant nativeApp
    (native_binding_invariant who value) players
  exact ⟨_, stateEq.symm, invariant.runRounds nativeScheduler control.remaining middle execution
    (invariant.resume control.actor control.execution middle stored middleMem) executionMem⟩

open Classical in
/-- The successful publication is exactly the owner's bound value. The
statement is about every supported continuation from every history in the
information set, rather than an almost-sure claim under the site's belief. -/
theorem native_sequentially_rational_opening_exact
    (assessment : nativeModel.BehavioralAssessment) (who : Player)
    (site : nativeModel.InformationSite who)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (siteEq : site.1 = some (past, view)) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store = some (.success bit))
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site (fun history => nativeUtility who history.state)
        (2 * nativeHorizon + 1)))
    (history : nativeModel.InformationHistory who site.1) (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom assessment.strategy
      (2 * nativeHorizon + 1) history.1).support) :
    nativePublicationAt who final.state = some (.success bit) := by
  obtain ⟨publishedBit, published⟩ := native_sequentially_rational_opening_succeeds assessment who
    site past view siteEq bit granted unfinished stored rational history final supported
  obtain ⟨control, stateEq, _, _, observed⟩ :=
    native_information_control who past view ⟨history.1, history.2.trans siteEq⟩
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  have binding :=
    (publication_site_facts who view control observed bit granted unfinished stored).2.2
  obtain ⟨result, finalEq, preserved⟩ := native_binding_continuation assessment.strategy control
    trace who (.success bit) binding final supported
  rcases final with ⟨finalState, finalTrace⟩
  change finalState = some result at finalEq
  subst finalState
  have provenance := native_publication_binding result.execution.application.config
    (native_history_reachable result finalTrace) who publishedBit
    (by simpa only [nativePublicationAt, Option.bind_some] using published)
  have same : publishedBit = bit := by
    rw [preserved] at provenance
    cases Option.some.inj provenance
    rfl
  simpa only [same] using published

end VegasTests.SelectiveAssociation
