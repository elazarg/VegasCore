/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeLaw
import VegasTests.MonitoredGuessingNativeResolutionFinal

/-! # Every type prefers the source-compatible silent initial response

Silence leads to Bob's ordinary guess law. A raw submission has continuation
value at most zero under the report charge, while truthful final opening after
silence gives the nonnegative probability of a correct guess. The comparison
allows Alice to replace her entire native policy, including her final response.
-/

noncomputable section
namespace VegasTests.MonitoredGuessing
open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem quiet_silent_to_bob (players : Player → nativeApp.Policy)
    (reports : players watcher = nativeWatcherPolicy) (bit : Bool) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.player watcher, .wire, .grant bobPublication, .player bob]
      (ambientRespond bit nativeSilent) =
      (players bob [] ((quietBob bit).observe nativeApp bob)).map
        ((quietBob bit).respond nativeApp bob) := by
  rw [show ([.player watcher, .wire, .grant bobPublication, .player bob] :
    List (ServiceInstruction nativeGraph)) = [.player watcher, .wire] ++
      [.grant bobPublication, .player bob] from rfl,
    runInteractionPlan_append, monitoring_plan players reports, silent_monitoring_law,
    FinDist.pure_bind]
  have quiet : monitoredPrefix bit nativeSilent ∅ = quietAfterWire bit := rfl
  rw [quiet]
  simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, quiet_grant,
    quiet_bob_activation, ReactiveApplication.resume, FinDist.pure_bind,
    ReactiveApplication.invoke, FinDist.bind_pure]
  rfl

theorem initial_silent_value (deposit : ℝ) (players : Player → nativeApp.Policy)
    (reports : players watcher = nativeWatcherPolicy) (guesses : FinDist Bool) (bit : Bool)
    (guessing : players bob [] ((quietBob bit).observe nativeApp bob) =
      guesses.map nativeGuessAction) :
    initialResponseValue deposit players bit nativeSilent =
      guesses.expect (fun guess =>
        (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork (nativePlan.drop 5)
          (quietGuessRespond bit guess)).expect (nativeExecutionUtility deposit alice)) := by
  unfold initialResponseValue
  rw [show nativePlan.tail = [.player watcher, .wire, .grant bobPublication, .player bob] ++
    nativePlan.drop 5 from rfl, runInteractionPlan_append, quiet_silent_to_bob players reports,
    guessing, FinDist.expect_bind, FinDist.expect_map, FinDist.expect_map]
  rfl

theorem initial_silent_value_le (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (players : Player → nativeApp.Policy) (reports : players watcher = nativeWatcherPolicy)
    (guesses : FinDist Bool) (bit : Bool)
    (guessing : players bob [] ((quietBob bit).observe nativeApp bob) =
      guesses.map nativeGuessAction) :
    initialResponseValue deposit players bit nativeSilent ≤ guesses.prob bit := by
  rw [initial_silent_value deposit players reports guesses bit guessing]
  have bound : ∀ guess : Bool,
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork (nativePlan.drop 5)
        (quietGuessRespond bit guess)).expect (nativeExecutionUtility deposit alice) ≤
          if bit = guess then 1 else 0 := by
    intro guess
    rw [show nativePlan.drop 5 = .includeLatest bobPublication bob :: nativePlan.drop 6 from rfl,
      runInteractionPlan, quiet_guess_included, FinDist.pure_bind]
    have result := resolution_plan_alice_upper deposit nonnegative players (nativePlan.drop 6)
      (quietGuessIncluded bit guess) bit (guessResult guess) (quiet_guess_fixed bit guess)
        (quiet_guess_results bit guess).1
    rw [(quiet_guess_results bit guess).2] at result
    convert result using 1
    cases bit <;> cases guess <;> norm_num [correctness, guessResult, rejectedAlice, alice, bob,
      PublicationResult.isSuccess]
  apply (FinDist.expect_mono (fun guess _ => bound guess)).trans_eq
  simpa only [mul_one] using FinDist.expect_ite_eq guesses bit 1

theorem initial_silent_value_eq (deposit : ℝ) (players : Player → nativeApp.Policy)
    (opens : players alice = nativeAlicePolicy) (reports : players watcher = nativeWatcherPolicy)
    (guesses : FinDist Bool) (bit : Bool)
    (guessing : players bob [] ((quietBob bit).observe nativeApp bob) =
      guesses.map nativeGuessAction) :
    initialResponseValue deposit players bit nativeSilent = guesses.prob bit := by
  rw [initial_silent_value deposit players reports guesses bit guessing]
  have exactValue : ∀ guess : Bool,
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork (nativePlan.drop 5)
        (quietGuessRespond bit guess)).expect (nativeExecutionUtility deposit alice) =
          if bit = guess then 1 else 0 := by
    intro guess
    have summarized := quiet_guess_suffix_summary players opens bit guess
    have value := congrArg (fun law => law.expect (fun result : Results × Bool =>
      utility result.1 alice - if result.2 then deposit else 0)) summarized
    rw [FinDist.expect_map, FinDist.expect_pure] at value
    convert value using 1
    · apply FinDist.expect_congr
      intro execution _
      simp only [nativeExecutionUtility, true_and]
    · cases bit <;> cases guess <;> norm_num [utility, correctness, openingPenalty,
        guessResult, alice, PublicationResult.isSuccess]
  simp_rw [exactValue]
  simpa only [mul_one] using FinDist.expect_ite_eq guesses bit 1

theorem initial_alice_site_dominates (deposit : ℝ) (sufficient : 2 ≤ deposit)
    (assessment : nativeModel.BehavioralAssessment) (guesses : FinDist Bool)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior)
    (atQuiet : assessment.strategy bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1)
    (bit : Bool) (alternative : nativeModel.BehavioralPolicy alice) :
    (assessment.continuationContext (initialAliceSite bit)
      (fun history => nativeUtility deposit alice history.state)
        (2 * nativeHorizon + 1)).value alternative ≤
    (assessment.continuationContext (initialAliceSite bit)
      (fun history => nativeUtility deposit alice history.state)
        (2 * nativeHorizon + 1)).value (assessment.strategy alice) := by
  let players := nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
    assessment.strategy
  let changed := nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
    (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy alice alternative)
  have opens : players alice = nativeAlicePolicy := by
    change nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler alice (assessment.strategy alice)) = _
    rw [alicePolicy, decode_native_alice]
  have reports : players watcher = nativeWatcherPolicy := by
    change nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler watcher (assessment.strategy watcher)) = _
    rw [watcherPolicy, decode_native_watcher]
  have changedReports : changed watcher = nativeWatcherPolicy := by
    change nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler watcher ((Profile.update (sig := nativeModel.behavioralSignature)
        assessment.strategy alice alternative) watcher)) = _
    rw [Profile.update_of_ne _ _ (by decide : watcher ≠ alice)]
    exact reports
  have guessing : players bob [] ((quietBob bit).observe nativeApp bob) =
      guesses.map nativeGuessAction := quiet_guess_policy assessment.strategy guesses atQuiet bit
  have changedGuessing : changed bob [] ((quietBob bit).observe nativeApp bob) =
      guesses.map nativeGuessAction := by
    change (nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler bob ((Profile.update (sig := nativeModel.behavioralSignature)
        assessment.strategy alice alternative) bob))) _ _ = _
    rw [Profile.update_of_ne _ _ (by decide : bob ≠ alice)]
    exact guessing
  rw [initial_alice_context_value, initial_alice_context_value, Profile.update_eq_self]
  change (changed alice [] ((aliceActivated bit).observe nativeApp alice)).expect _ ≤
    (players alice [] ((aliceActivated bit).observe nativeApp alice)).expect _
  rw [opens]
  change _ ≤ (FinDist.pure nativeSilent).expect (initialResponseValue deposit players bit)
  rw [FinDist.expect_pure,
    initial_silent_value_eq deposit players opens reports guesses bit guessing]
  apply FinDist.expect_le_of_forall
  intro action supported
  have covered := nativeMenu.decode_embedPolicy_covered nativeInitialLaw nativeHorizon
    nativeScheduler alice ((Profile.update (sig := nativeModel.behavioralSignature)
      assessment.strategy alice alternative) alice) []
      ((aliceActivated bit).observe nativeApp alice) action supported
  rcases initial_response_cases bit action covered with rfl | ⟨submission, rfl⟩
  · exact initial_silent_value_le deposit (by linarith) changed changedReports guesses bit
      changedGuessing
  · exact (initial_submission_value_nonpositive deposit sufficient changed changedReports bit
      submission).trans (guesses.prob_nonneg bit)

end VegasTests.MonitoredGuessing
