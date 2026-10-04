/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.RestrictedGuessOutcome
import Vegas.Examples.SelectiveAssociation.GuessIncentives

/-! # Native guessing incentives under the posterior comparison

Every whole-policy deviation is a mixture of fixed current responses. Each
fixed response has one binding result throughout the information set. Thus
only the posterior masses of Alice's two successful bindings enter the
comparison. Failed Alice bindings contribute zero to both successful guesses.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem expected_guessReward_success (assessment : model.BehavioralAssessment)
    (who : Player) (site : model.InformationSite who) (bit : Bool) :
    expect (assessment.belief who site) (fun history =>
      guessReward (.success bit) history.1.state) =
        ((assessment.belief who site).toOuterMeasure
            {history | hasAliceBit bit history.1.state}).toReal := by
  classical
  exact expect_indicator _ _

theorem prescribed_guess_optimal (assessment : model.BehavioralAssessment)
    (who : Player) (site : model.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (posterior : publicGuess view = false →
      ((assessment.belief who site).toOuterMeasure
          {history | hasAliceBit true history.1.state}).toReal ≤
        ((assessment.belief who site).toOuterMeasure
            {history | hasAliceBit false history.1.state}).toReal)
    (guess : PublicationResult Bool) :
    expect (assessment.belief who site) (fun history => guessReward guess history.1.state) ≤
      expect (assessment.belief who site) (fun history =>
        guessReward (.success (publicGuess view)) history.1.state) := by
  classical
  cases selected : publicGuess view with
  | false =>
      cases guess with
      | failure =>
          exact expect_mono (fun history _ => guessReward_nonneg _ history.1.state)
              (payoffIntegrable_of_finite _ _)
            (payoffIntegrable_of_finite _ _)
      | success bit =>
          rw [expected_guessReward_success, expected_guessReward_success]
          cases bit
          · exact le_rfl
          · exact posterior selected
  | true =>
      have target : expect (assessment.belief who site) (fun history =>
          guessReward (.success true) history.1.state) = 1 := by
        refine (expect_congr_on_support (g := fun _ => (1 : ℝ)) ?_).trans
          (expect_constant _ _)
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
      exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
          (fun history _ => guessReward_le_one _ _)

open Classical in
theorem committed_guesser_bound (assessment : model.BehavioralAssessment)
    (who : Player) (guesser : who ≠ alice) (site : model.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (turn : nativeTurnEvent? who past.length = some (nativeBindingEvent who))
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
  obtain ⟨control, stateEq, active, recalled, observed⟩ := information_control who past view history
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  have ownerTurn : NativeTurn (nativeBindingEvent who) control :=
    .of_turnEvent? active (by rw [recalled]; exact turn)
  obtain ⟨result, resultEq, bound⟩ := guesser_continuation_bound who guesser changed
    (update_opens_other who alice (Ne.symm guesser) _)
      control trace active ownerTurn final supported
  have same := native_committed_binding_local (observation := leaks) who
    (Profile.update (sig := model.behavioralSignature) profile who alternative) past view turn
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
    (turn : nativeTurnEvent? who past.length = some (nativeBindingEvent who)) :
    (assessment.truncatedContinuationContext site (fun history => nativeUtility who history.state)
      (2 * nativeHorizon + 1)).value (assessment.strategy who) =
      expect (assessment.belief who site) (fun history =>
        guessReward (.success (publicGuess view)) history.1.state) := by
  simp only [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    Profile.update_eq_self, expect_bind_of_finite, strategy]
  apply expect_congr_on_support
  intro history _
  obtain ⟨control, stateEq, active, recalled, observed⟩ := information_control who past view
    ⟨history.1, history.2.trans information⟩
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  refine (expect_congr_on_support (g := fun _ =>
    guessReward (.success (publicGuess view)) (some control)) ?_).trans
      (expect_constant _ _)
  intro final supported
  have ownerTurn : NativeTurn (nativeBindingEvent who) control :=
    .of_turnEvent? active (by rw [recalled]; exact turn)
  simpa only [observed] using profile_guesser_payoff who guesser control trace active ownerTurn
    final supported

/-- Whole-policy sequential rationality at either native guessing site.
The only belief obligation is the stated comparison at uncertified views. -/
theorem profile_guesser_rational (assessment : model.BehavioralAssessment)
    (strategy : assessment.strategy = profile) (who : Player) (guesser : who ≠ alice)
    (site : model.InformationSite who) (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (turn : nativeTurnEvent? who past.length = some (nativeBindingEvent who))
    (posterior : publicGuess view = false →
      ((assessment.belief who site).toOuterMeasure
          {history | hasAliceBit true history.1.state}).toReal ≤
        ((assessment.belief who site).toOuterMeasure
            {history | hasAliceBit false history.1.state}).toReal) :
    assessment.IsSequentiallyRationalAt site (assessment.truncatedContinuationContext site
      (fun history => nativeUtility who history.state) (2 * nativeHorizon + 1)) := by
  classical
  refine (Context.isLocallyOptimal_iff_of_integrable
    (nativeUtility_continuation_integrable assessment site _ _)
      fun _ _ => nativeUtility_continuation_integrable assessment site _ _).mpr
        fun alternative _ => ?_
  have once : model.ActsOnceWhereItMatters := model.actsOnceWhereItMatters_of_actsOnce
    (InformationModel.actsOnce_of_decisionInformationAntichain
      (menu.decisionInformationAntichain (PMF.pure nativeInitial) nativeHorizon scheduler))
  rw [show (assessment.truncatedContinuationContext site
      (fun history => nativeUtility who history.state) (2 * nativeHorizon + 1)).value alternative =
      _ from assessment.continuationContextWith_value_eq_expect_commit
    (model.truncatedRunner (2 * nativeHorizon + 1)) site
    (model.runnerFactorsAt_truncated once
      (menu.informationSite_allNonterminal (PMF.pure nativeInitial) nativeHorizon scheduler
        who site) (2 * nativeHorizon)) _ alternative
      (nativeUtility_continuation_integrable assessment site _ _),
    profile_guesser_context assessment strategy who guesser site past view information turn]
  refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun choice _ => ?_
  obtain ⟨guess, bound⟩ := committed_guesser_bound assessment who guesser site past view
    information turn alternative choice
  calc
    _ ≤ expect (assessment.belief who site) (fun history => guessReward guess history.1.state) := by
      simp only [InformationModel.BehavioralAssessment.continuationContextWith_value,
        InformationModel.truncatedRunner, expect_bind_of_finite, strategy]
      refine expect_mono (fun history _ => ?_) (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _)
      exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ (bound history)
    _ ≤ _ := prescribed_guess_optimal assessment who site past view information posterior guess

end Vegas.Examples.SelectiveAssociation.Restricted
