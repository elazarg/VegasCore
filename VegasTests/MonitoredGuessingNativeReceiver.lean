/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeBeliefs
import VegasTests.MonitoredGuessingNativeLaw

/-! # The prescribed receiver's value at the actual quiet information site -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

theorem quiet_prescribed_finish_value (profile : Profile nativeModel.behavioralSignature)
    (guesses : FinDist Bool) (deposit : ℝ)
    (alicePolicy : profile alice = nativeAliceBehavior)
    (atQuiet : profile bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1)
    (bit : Bool) :
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
        (quietBobHistory bit).state).expect (nativeUtility deposit bob) =
      guesses.expect (fun guess => correctness (.success bit) (guessResult guess)) := by
  let players := nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile
  have aliceEq : players alice = nativeAlicePolicy := by
    change nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler alice (profile alice)) = _
    rw [alicePolicy, decode_native_alice]
  have finishLaw := native_finish_response players
    [.player alice, .player watcher, .wire, .grant bobPublication]
    ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
      .grant alicePublication, .player alice] ++ resolutionTail) bob rfl (quietBob bit) rfl
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
    (quietBobHistory bit).state = _ at finishLaw
  change (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
    (quietBobHistory bit).state).expect _ = _
  have decision : players bob ((quietBob bit).recall bob)
      ((quietBob bit).observe nativeApp bob) = guesses.map nativeGuessAction :=
    quiet_guess_policy profile guesses atQuiet bit
  rw [finishLaw, decision]
  simp only [FinDist.bind_map, FinDist.expect_bind, FinDist.expect_map]
  apply FinDist.expect_congr
  intro guess _
  have value := congrArg (fun law : FinDist (Results × Bool) =>
    law.expect (fun result => utility result.1 bob))
      (quiet_guess_suffix_summary players aliceEq bit guess)
  simp only [FinDist.expect_map, FinDist.expect_pure, utility_bob] at value
  change FinDist.expect _ (fun final => nativeExecutionUtility deposit bob final) = _
  simp only [nativeExecutionUtility, show bob ≠ alice by decide, false_and,
    ↓reduceIte, sub_zero, utility_bob]
  exact value

theorem fair_correctness (guess : PublicationResult Bool) :
    (FinDist.uniformOfFintype (α := Bool)).expect
      (fun bit => correctness (.success bit) guess) = (1 / 2 : ℝ) := by
  simp only [FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype,
    Fintype.card_bool, Fintype.sum_bool]
  cases guess <;> norm_num [correctness, PublicationResult.isSuccess]

theorem quiet_prescribed_context_value (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (guesses : FinDist Bool) (deposit : ℝ)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior)
    (atQuiet : assessment.strategy bob quietBobSite.1 =
      nativeGuessBehavior guesses quietBobSite.1) :
    (assessment.continuationContext quietBobSite
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        (assessment.strategy bob) = (1 / 2 : ℝ) := by
  rw [quiet_native_context assessment consistent alicePolicy watcherPolicy]
  simp only [Profile.update_eq_self]
  simp_rw [quiet_prescribed_finish_value assessment.strategy guesses deposit alicePolicy atQuiet]
  rw [FinDist.expect_comm]
  simp only [fair_correctness, FinDist.expect_const]

end VegasTests.MonitoredGuessing
