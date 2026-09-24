/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGuessOpenings

/-! # Sequential rationality makes Bob match a certified Alice binding

All native raw responses are retained. A wrong response is uniformly worse
than the feasible correction, including at histories assigned zero belief.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

open Classical in
theorem native_supported_certified_guess
    (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (site : nativeModel.InformationSite bob)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (siteEq : site.1 = some (past, view)) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (unfinished : bobBinding ∉ view.application.publicView.observation.completionOrder)
    (observed : nativeRuntime.bindingEvidenceObserved nativeLeaks view (aliceBindingEvidence bit))
    (choice : nativeModel.Choice bob site.1)
    (chosen : choice ∈ (assessment.strategy bob site.1).support)
    (history : nativeModel.InformationHistory bob site.1) (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
        ((assessment.strategy bob).commit site.1 choice))
          (2 * nativeHorizon + 1) history.1).support) :
    nativeBobBindingAt final.state = some (.success bit) := by
  rcases site with ⟨info, isSite⟩
  change info = some (past, view) at siteEq
  subst info
  by_contra wrong
  have once := nativeModel.actsOnceWhereItMatters_of_actsOnce
    (InformationModel.actsOnce_of_decisionInformationAntichain
      (nativeMenu.decisionInformationAntichain (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler))
  apply (assessment.not_supported_choice_of_uniform_gap once ⟨some (past, view), isSite⟩
    (nativeMenu.informationSite_allNonterminal (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler bob ⟨some (past, view), isSite⟩)
    (fun outcome => nativeUtility bob outcome.state) (2 * nativeHorizon)
    (rational bob ⟨some (past, view), isSite⟩) choice
    ((assessment.strategy bob).commit (some (past, view)) (bobCorrectiveChoice bit past view))
    0 1 (by norm_num) _ _) chosen
  · intro other
    apply FinDist.expect_le_of_forall
    intro otherFinal otherSupported
    have same := native_committed_bob_binding_local assessment.strategy past view granted
      unfinished choice history other final otherFinal supported otherSupported
    have initial := native_observed_alice_binding past view bit observed other
    obtain ⟨control, stateEq, _, _, _⟩ := native_information_control bob past view other
    rcases other with ⟨⟨state, trace⟩, information⟩
    change state = some control at stateEq
    subst state
    obtain ⟨result, resultEq, preserved⟩ := native_binding_continuation _ control trace alice
      (.success bit) initial otherFinal otherSupported
    rcases otherFinal with ⟨finalState, finalTrace⟩
    change finalState = some result at resultEq
    subst finalState
    apply native_bob_wrong_binding_bound result finalTrace bit preserved
    intro correct
    exact wrong (same.trans correct)
  · intro other
    calc
      1 = (nativeModel.runBehavioralFrom
          (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
            ((assessment.strategy bob).commit (some (past, view))
              (bobCorrectiveChoice bit past view))) (2 * nativeHorizon + 1) other.1).expect
            (fun _ => 1) := (FinDist.expect_const _ _).symm
      _ ≤ _ := FinDist.expect_mono fun outcome member =>
        le_of_eq (native_bob_corrective_utility assessment rational past view bit granted unfinished
          observed other outcome member).symm

/-- The protected visit has not yet settled its event at any compatible legal
history. This is derived from the actual service, not required of the view. -/
theorem native_bob_view_unfinished (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (history : nativeModel.InformationHistory bob (some (past, view))) :
    bobBinding ∉ view.application.publicView.observation.completionOrder := by
  obtain ⟨control, stateEq, active, _, observed⟩ := native_information_control bob past view history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  rw [← observed] at granted ⊢
  have unfinished := native_decision_unfinished bobBinding control trace bob active granted
  change bobBinding ∉
    control.execution.application.config.history.map EventGraph.Completion.event
  intro completed
  exact unfinished ((control.execution.application.config.history_exact _).mp completed)

open Classical in
/-- Under the complete mixed sequentially rational strategy, every compatible
history at Bob's certified binding decision ends with matching successful
Alice and Bob publications, and gives Bob utility one. -/
theorem native_sequentially_rational_certified_guess
    (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (site : nativeModel.InformationSite bob)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (siteEq : site.1 = some (past, view)) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (observed : nativeRuntime.bindingEvidenceObserved nativeLeaks view (aliceBindingEvidence bit))
    (history : nativeModel.InformationHistory bob site.1) (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom assessment.strategy
      (2 * nativeHorizon + 1) history.1).support) :
    nativePublicationAt alice final.state = some (.success bit) ∧
      nativePublicationAt bob final.state = some (.success bit) ∧
        nativeUtility bob final.state = 1 := by
  rcases site with ⟨info, isSite⟩
  change info = some (past, view) at siteEq
  subst info
  have unfinished := native_bob_view_unfinished past view granted history
  have once := nativeModel.actsOnceWhereItMatters_of_actsOnce
    (InformationModel.actsOnce_of_decisionInformationAntichain
      (nativeMenu.decisionInformationAntichain (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler))
  have law := nativeModel.runBehavioralFrom_update_withLaw_eq_bind once assessment.strategy bob
    (assessment.strategy bob) (some (past, view)) (assessment.strategy bob (some (past, view)))
    history.1 history.2
    (nativeMenu.informationSite_allNonterminal (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler bob ⟨some (past, view), isSite⟩ history)
    (InformationModel.InformationSite.active nativeModel ⟨some (past, view), isSite⟩ history)
    (2 * nativeHorizon)
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self] at law
  rw [law] at supported
  obtain ⟨choice, chosen, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have correct := native_supported_certified_guess assessment rational ⟨some (past, view), isSite⟩
    past view rfl bit granted unfinished observed choice chosen history final finalMem
  have aliceOpens := native_bob_committed_alice_opens assessment rational past view bit granted
    observed choice history final finalMem
  have bobOpens := native_bob_committed_bob_opens assessment rational past view bit granted choice
    history final finalMem correct
  refine ⟨aliceOpens, bobOpens, ?_⟩
  cases finalEq : final.state with
  | none =>
      simp only [nativePublicationAt, finalEq, Option.bind_none] at aliceOpens
      cases aliceOpens
  | some result =>
      simp only [nativePublicationAt, finalEq, Option.bind_some] at aliceOpens bobOpens
      change alicePublicationRef.get? result.execution.application.config.store = _ at aliceOpens
      change bobPublicationRef.get? result.execution.application.config.store = _ at bobOpens
      change utility (nativeResults result.execution.application.config) bob = 1
      apply (utility_bob_eq_one_iff _).mpr
      exact ⟨bit, by simp only [nativeResults, aliceOpens, Option.getD_some],
        by simp only [nativeResults, bobOpens, Option.getD_some]⟩

end VegasTests.SelectiveAssociation
