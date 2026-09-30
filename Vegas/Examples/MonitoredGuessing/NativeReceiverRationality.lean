/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeReceiver
import Vegas.Examples.MonitoredGuessing.NativeReceiverValue
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Rationality of every source guessing mixture at the quiet native site -/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

theorem quiet_raw_finish_value_le (deposit : ℝ) (players : Player → nativeApp.Policy)
    (bit : Bool) :
    expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
      (quietBobHistory bit).state) (nativeUtility deposit bob) ≤
      expect (players bob [] ((quietBob false).observe nativeApp bob))
        (fun response => correctness (.success bit) (quietGuess response players)) := by
  have finishLaw := native_finish_response players
    [.player alice, .player watcher, .wire, .grant bobPublication]
    (nativePlan.drop 5) bob rfl (quietBob bit) rfl
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
    (quietBobHistory bit).state = _ at finishLaw
  rw [finishLaw, expect_bind_tower _ _ _
      (payoffIntegrable_of_bounded _ _ (nativeUtility_abs_le deposit bob)),
    quiet_bob_recall, quiet_bob_observation]
  refine expect_mono (fun response _ => ?_)
    (payoffIntegrable_expect_of_bounded _ _ _ (by positivity) (nativeUtility_abs_le deposit bob))
    (payoffIntegrable_of_finite_summary _ (fun response => quietGuess response players)
      (correctness (.success bit)))
  rw [expect_map]
  exact quiet_response_bob_value_le deposit players bit response

theorem quiet_receiver_context_le (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain) (deposit : ℝ)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior)
    (alternative : nativeModel.BehavioralPolicy bob) :
    (assessment.truncatedContinuationContext quietBobSite
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        alternative ≤ (1 / 2 : ℝ) := by
  rw [quiet_native_context assessment consistent alicePolicy watcherPolicy]
  let players := nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
    (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob alternative)
  calc
    _ ≤ expect (PMF.uniformOfFintype Bool) (fun bit =>
        expect (players bob [] ((quietBob false).observe nativeApp bob))
          (fun response => correctness (.success bit) (quietGuess response players))) :=
      expect_mono (fun bit _ => quiet_raw_finish_value_le deposit players bit)
          (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _)
    _ = _ := by
      rw [expect_comm_of_support_finite_left _ _ (Set.toFinite _) _ fun bit _ =>
        payoffIntegrable_of_finite_summary _ (fun response => quietGuess response players)
          (correctness (.success bit))]
      simp only [fair_correctness, expect_constant]

theorem quiet_receiver_site_dominates (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (guesses : PMF Bool) (deposit : ℝ)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior)
    (atQuiet : assessment.strategy bob quietBobSite.1 =
      nativeGuessBehavior guesses quietBobSite.1)
    (alternative : nativeModel.BehavioralPolicy bob) :
    (assessment.truncatedContinuationContext quietBobSite
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        alternative ≤
    (assessment.truncatedContinuationContext quietBobSite
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        (assessment.strategy bob) := by
  rw [quiet_prescribed_context_value assessment consistent guesses deposit
    alicePolicy watcherPolicy atQuiet]
  exact quiet_receiver_context_le assessment consistent deposit alicePolicy watcherPolicy
    alternative

end Vegas.Examples.MonitoredGuessing
