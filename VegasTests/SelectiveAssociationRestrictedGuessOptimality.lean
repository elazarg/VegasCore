/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedGuessOutcome
import VegasTests.SelectiveAssociationGuessIncentives

/-! # Native guessing incentives under the posterior comparison

Every whole-policy deviation is a mixture of fixed current responses. Each
fixed response has one binding result throughout the information set. Thus
only the posterior masses of Alice's two successful bindings enter the
comparison. Failed Alice bindings contribute zero to both successful guesses.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem expected_guessReward_success (assessment : model.BehavioralAssessment)
    (who : Player) (site : model.InformationSite who) (bit : Bool) :
    (assessment.belief who site).expect (fun history =>
      guessReward (.success bit) history.1.state) =
        (assessment.belief who site).probOf {history | hasAliceBit bit history.1.state} := by
  classical
  exact FinDist.expect_indicator_eq_probOf _ _

theorem prescribed_guess_optimal (assessment : model.BehavioralAssessment)
    (who : Player) (site : model.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (posterior : publicGuess view = false →
      (assessment.belief who site).probOf {history | hasAliceBit true history.1.state} ≤
        (assessment.belief who site).probOf {history | hasAliceBit false history.1.state})
    (guess : PublicationResult Bool) :
    (assessment.belief who site).expect (fun history => guessReward guess history.1.state) ≤
      (assessment.belief who site).expect (fun history =>
        guessReward (.success (publicGuess view)) history.1.state) := by
  classical
  cases selected : publicGuess view with
  | false =>
      cases guess with
      | failure =>
          exact FinDist.expect_mono (fun history _ => guessReward_nonneg _ history.1.state)
      | success bit =>
          rw [expected_guessReward_success, expected_guessReward_success]
          cases bit
          · exact le_rfl
          · exact posterior selected
  | true =>
      have target : (assessment.belief who site).expect (fun history =>
          guessReward (.success true) history.1.state) = 1 := by
        refine (FinDist.expect_congr (v := fun _ => (1 : ℝ)) ?_).trans
          (FinDist.expect_const _ _)
        intro history _
        have known := publicGuess_true_known who past view selected
          ⟨history.1, history.2.trans information⟩
        obtain ⟨control, stateEq, _, _, _⟩ := information_control who past view
          ⟨history.1, history.2.trans information⟩
        have valid : hasAliceBit true history.1.state := by
          rw [hasAliceBit, stateEq]
          rw [stateEq] at known
          exact known
        simp only [guessReward, ite_eq_left valid]
      rw [target]
      exact FinDist.expect_le_of_forall _ _ _ (fun history _ => guessReward_le_one _ _)

open Classical in
theorem committed_guesser_bound (assessment : model.BehavioralAssessment)
    (who : Player) (guesser : who ≠ alice) (site : model.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (granted : view.application.publicView.serviceGrant = some (nativeBindingEvent who))
    (alternative : model.BehavioralPolicy who) (choice : model.Choice who site.1) :
    ∃ guess : PublicationResult Bool,
      ∀ history : model.InformationHistory who site.1, ∀ final : arena.History,
        final ∈ (model.runBehavioralFrom
          (Profile.update (sig := model.behavioralSignature) profile who
            (alternative.commit site.1 choice)) (2 * nativeHorizon + 1) history.1).support →
        nativeUtility who final.state ≤ guessReward guess history.1.state := by
  classical
  rcases site with ⟨info, isSite⟩
  change info = some (past, view) at information
  subst info
  obtain ⟨reference, _⟩ := (assessment.belief who ⟨some (past, view), isSite⟩).support_nonempty
  let changed := Profile.update (sig := model.behavioralSignature) profile who
    (alternative.commit (some (past, view)) choice)
  obtain ⟨referenceFinal, referenceMem⟩ := (model.runBehavioralFrom changed
    (2 * nativeHorizon + 1) reference.1).support_nonempty
  refine ⟨(nativeBindingAt who referenceFinal.state).getD .failure, ?_⟩
  intro history final supported
  obtain ⟨control, stateEq, active, _, observed⟩ := information_control who past view history
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  have grant : control.execution.application.serviceGrant = some (nativeBindingEvent who) := by
    rw [← observed] at granted
    exact granted
  obtain ⟨result, resultEq, bound⟩ := guesser_continuation_bound who guesser changed
    (update_opens_other who alice (Ne.symm guesser) _) control trace active grant final supported
  have same := native_committed_binding_local (observation := leaks) who
    (Profile.update (sig := model.behavioralSignature) profile who alternative) past view granted
      choice ⟨⟨some control, trace⟩, historyInfo⟩ reference final referenceFinal
        (by simpa only [Profile.update_same, Profile.update_idem] using supported)
        (by simpa only [Profile.update_same, Profile.update_idem] using referenceMem)
  have valueEq : (nativeBindingAt who referenceFinal.state).getD .failure =
      ((nativeBindingRef who).get? result.execution.application.config.store).getD .failure := by
    rw [← same, nativeBindingAt, resultEq, Option.bind_some]
  rw [valueEq]
  exact bound

theorem profile_guesser_context (assessment : model.BehavioralAssessment)
    (strategy : assessment.strategy = profile) (who : Player) (guesser : who ≠ alice)
    (site : model.InformationSite who) (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (granted : view.application.publicView.serviceGrant = some (nativeBindingEvent who)) :
    (assessment.continuationContext site (fun history => nativeUtility who history.state)
      (2 * nativeHorizon + 1)).value (assessment.strategy who) =
      (assessment.belief who site).expect (fun history =>
        guessReward (.success (publicGuess view)) history.1.state) := by
  simp only [InformationModel.BehavioralAssessment.continuationContext_value,
    Profile.update_eq_self, FinDist.expect_bind, strategy]
  apply FinDist.expect_congr
  intro history _
  obtain ⟨control, stateEq, active, _, observed⟩ := information_control who past view
    ⟨history.1, history.2.trans information⟩
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  refine (FinDist.expect_congr (v := fun _ =>
    guessReward (.success (publicGuess view)) (some control)) ?_).trans
      (FinDist.expect_const _ _)
  intro final supported
  have grant : control.execution.application.serviceGrant = some (nativeBindingEvent who) := by
    rw [← observed] at granted
    exact granted
  simpa only [observed] using profile_guesser_payoff who guesser control trace active grant final
    supported

/-- Whole-policy sequential rationality at either native guessing site.
The only belief obligation is the stated comparison at uncertified views. -/
theorem profile_guesser_rational (assessment : model.BehavioralAssessment)
    (strategy : assessment.strategy = profile) (who : Player) (guesser : who ≠ alice)
    (site : model.InformationSite who) (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (granted : view.application.publicView.serviceGrant = some (nativeBindingEvent who))
    (posterior : publicGuess view = false →
      (assessment.belief who site).probOf {history | hasAliceBit true history.1.state} ≤
        (assessment.belief who site).probOf {history | hasAliceBit false history.1.state}) :
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext site
      (fun history => nativeUtility who history.state) (2 * nativeHorizon + 1)) := by
  classical
  intro alternative _
  have once : model.ActsOnceWhereItMatters := model.actsOnceWhereItMatters_of_actsOnce
    (InformationModel.actsOnce_of_decisionInformationAntichain
      (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon scheduler))
  rw [assessment.continuationContext_value_eq_expect_commit once site
    (menu.informationSite_allNonterminal (FinDist.pure nativeInitial) nativeHorizon scheduler
      who site) _ (2 * nativeHorizon) alternative,
    profile_guesser_context assessment strategy who guesser site past view information granted]
  apply FinDist.expect_le_of_forall
  intro choice _
  obtain ⟨guess, bound⟩ := committed_guesser_bound assessment who guesser site past view
    information granted alternative choice
  calc
    _ ≤ (assessment.belief who site).expect (fun history => guessReward guess history.1.state) := by
      simp only [InformationModel.BehavioralAssessment.continuationContext_value,
        FinDist.expect_bind, strategy]
      apply FinDist.expect_mono
      intro history _
      exact FinDist.expect_le_of_forall _ _ _ (bound history)
    _ ≤ _ := prescribed_guess_optimal assessment who site past view information posterior guess

end VegasTests.SelectiveAssociation.Restricted
