/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeReceiver
import VegasTests.MonitoredGuessingNativeReceiverValue

/-! # Rationality of every source guessing mixture at the quiet native site -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

theorem quiet_raw_finish_value_le (deposit : ℝ) (players : Player → nativeApp.Policy)
    (bit : Bool) :
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
      (quietBobHistory bit).state).expect (nativeUtility deposit bob) ≤
      (players bob [] ((quietBob false).observe nativeApp bob)).expect
        (fun response => correctness (.success bit) (quietGuess response players)) := by
  have finishLaw := native_finish_response players
    [.player alice, .player watcher, .wire, .grant bobPublication]
    (nativePlan.drop 5) bob rfl (quietBob bit) rfl
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
    (quietBobHistory bit).state = _ at finishLaw
  rw [finishLaw, FinDist.expect_bind, quiet_bob_recall, quiet_bob_observation]
  apply FinDist.expect_mono
  intro response _
  rw [FinDist.expect_map]
  exact quiet_response_bob_value_le deposit players bit response

theorem quiet_receiver_context_le (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain) (deposit : ℝ)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior)
    (alternative : nativeModel.BehavioralPolicy bob) :
    (assessment.continuationContext quietBobSite
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        alternative ≤ (1 / 2 : ℝ) := by
  rw [quiet_native_context assessment consistent alicePolicy watcherPolicy]
  let players := nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
    (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob alternative)
  calc
    _ ≤ (FinDist.uniformOfFintype (α := Bool)).expect (fun bit =>
        (players bob [] ((quietBob false).observe nativeApp bob)).expect
          (fun response => correctness (.success bit) (quietGuess response players))) :=
      FinDist.expect_mono (fun bit _ => quiet_raw_finish_value_le deposit players bit)
    _ = _ := by
      rw [FinDist.expect_comm]
      simp only [fair_correctness, FinDist.expect_const]

theorem quiet_receiver_site_dominates (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (guesses : FinDist Bool) (deposit : ℝ)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior)
    (atQuiet : assessment.strategy bob quietBobSite.1 =
      nativeGuessBehavior guesses quietBobSite.1)
    (alternative : nativeModel.BehavioralPolicy bob) :
    (assessment.continuationContext quietBobSite
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        alternative ≤
    (assessment.continuationContext quietBobSite
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        (assessment.strategy bob) := by
  rw [quiet_prescribed_context_value assessment consistent guesses deposit
    alicePolicy watcherPolicy atQuiet]
  exact quiet_receiver_context_le assessment consistent deposit alicePolicy watcherPolicy
    alternative

end VegasTests.MonitoredGuessing
