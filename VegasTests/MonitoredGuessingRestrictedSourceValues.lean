/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingRestrictedEvaluation

/-! # Source continuation incentives for arbitrary result utilities -/

noncomputable section

namespace VegasTests.MonitoredGuessing.Restricted

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def decisionResult (bit guess disclose : Bool) : Results :=
  ⟨if disclose then .success bit else .failure, guessResult guess⟩

def sourceResultUtility (reward : Results → Player → ℝ) : sourceArena.State → Player → ℝ
  | some (.inr (.inr config)), who => reward (sourceResults config.state) who
  | _, _ => 0

def sourceResultPayoff (reward : Results → Player → ℝ) (who : Player)
    (history : sourceArena.History) : ℝ := sourceResultUtility reward history.state who

theorem source_result_alice_value (reward : Results → Player → ℝ)
    (profile : Profile sourceModel.behavioralSignature) (bit guess : Bool) :
    (sourceModel.runBehavioralFrom profile 3 (SourcePath.guessed bit guess).history).expect
      (sourceResultPayoff reward alice) =
      (sourceDisclosures profile bit guess).expect fun disclose =>
        reward (decisionResult bit guess disclose) alice := by
  unfold sourceResultPayoff
  have value := congrArg (fun law : FinDist sourceArena.State =>
    law.expect (sourceResultUtility reward · alice)) (source_alice_run profile bit guess)
  simpa only [FinDist.expect_map, sourceDisclosures,
    sourceResultUtility, SourcePath.state, source_results, decisionResult] using value

theorem source_result_bob_value (reward : Results → Player → ℝ)
    (profile : Profile sourceModel.behavioralSignature) (bit : Bool) :
    (sourceModel.runBehavioralFrom profile 3 (SourcePath.drawn bit).history).expect
      (sourceResultPayoff reward bob) =
      (sourceGuesses profile).expect fun guess =>
        (sourceDisclosures profile bit guess).expect fun disclose =>
          reward (decisionResult bit guess disclose) bob := by
  unfold sourceResultPayoff
  have value := congrArg (fun law : FinDist sourceArena.State =>
    law.expect (sourceResultUtility reward · bob)) (source_bob_run profile bit)
  simpa only [FinDist.expect_map, FinDist.expect_bind,
    sourceGuesses, sourceDisclosures, sourceResultUtility, SourcePath.state,
    source_results, decisionResult] using value

theorem source_result_alice_context (reward : Results → Player → ℝ)
    (assessment : sourceModel.BehavioralAssessment) (bit guess : Bool)
    (alternative : sourceModel.BehavioralPolicy alice) :
    (assessment.continuationContext (sourceAliceSite bit guess)
      (sourceResultPayoff reward alice) 3).value alternative =
      (sourceDisclosures (Profile.update (sig := sourceModel.behavioralSignature)
        assessment.strategy alice alternative) bit guess).expect
        fun disclose => reward (decisionResult bit guess disclose) alice := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  calc
    _ = (assessment.belief alice (sourceAliceSite bit guess)).expect (fun _ =>
        (sourceDisclosures (Profile.update (sig := sourceModel.behavioralSignature)
          assessment.strategy alice alternative) bit guess).expect
          fun disclose => reward (decisionResult bit guess disclose) alice) := by
      apply FinDist.expect_congr
      intro history _
      rw [source_alice_history_unique bit guess history, source_result_alice_value]
    _ = _ := FinDist.expect_const ..

theorem source_result_bob_context (reward : Results → Player → ℝ)
    (assessment : sourceModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent sourceAntichain)
    (alternative : sourceModel.BehavioralPolicy bob) :
    (assessment.continuationContext sourceBobSite (sourceResultPayoff reward bob) 3).value
        alternative =
      (FinDist.uniformOfFintype (α := Bool)).expect fun bit =>
        (sourceGuesses (Profile.update (sig := sourceModel.behavioralSignature)
          assessment.strategy bob alternative)).expect fun guess =>
          (sourceDisclosures assessment.strategy bit guess).expect fun disclose =>
            reward (decisionResult bit guess disclose) bob := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, FinDist.expect_bind,
    source_consistent_bob assessment consistent, FinDist.expect_map]
  apply FinDist.expect_congr
  intro bit _
  change (sourceModel.runBehavioralFrom (Profile.update (sig := sourceModel.behavioralSignature)
    assessment.strategy bob alternative)
    3 (SourcePath.drawn bit).history).expect (sourceResultPayoff reward bob) = _
  rw [source_result_bob_value]
  apply FinDist.expect_congr
  intro guess _
  simp only [sourceDisclosures, sourceDecisionLaw, sourceChoice,
    Profile.update_of_ne _ _ (by decide : alice ≠ bob)]

theorem source_disclosure_optimal (reward : Results → Player → ℝ)
    (assessment : sourceModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin (sourceResultPayoff reward) 3)
    (bit guess disclose : Bool) :
    reward (decisionResult bit guess disclose) alice ≤
      (sourceDisclosures assessment.strategy bit guess).expect fun decision =>
        reward (decisionResult bit guess decision) alice := by
  let alternative := (sourceProfile (FinDist.pure false) (FinDist.pure disclose)) alice
  have optimal := rational alice (sourceAliceSite bit guess) alternative (Set.mem_univ _)
  change (assessment.continuationContext (sourceAliceSite bit guess)
    (sourceResultPayoff reward alice) 3).value alternative ≤ _ at optimal
  rw [source_result_alice_context, source_result_alice_context,
    Profile.update_eq_self] at optimal
  have chosen : sourceDisclosures (Profile.update (sig := sourceModel.behavioralSignature)
      assessment.strategy alice alternative)
      bit guess = FinDist.pure disclose := by
    simpa only [sourceDisclosures, sourceDecisionLaw, sourceChoice, Profile.update_same,
      alternative, sourceAliceSite, InformationModel.informationSite] using
        profile_opening_law (FinDist.pure false) (FinDist.pure disclose) bit guess
  rwa [chosen, FinDist.expect_pure] at optimal

theorem source_guess_optimal (reward : Results → Player → ℝ)
    (assessment : sourceModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent sourceAntichain)
    (rational : assessment.IsSequentiallyRationalWithin (sourceResultPayoff reward) 3)
    (guess : Bool) :
    (FinDist.uniformOfFintype (α := Bool)).expect (fun bit =>
      (sourceDisclosures assessment.strategy bit guess).expect fun disclose =>
        reward (decisionResult bit guess disclose) bob) ≤
      (FinDist.uniformOfFintype (α := Bool)).expect (fun bit =>
        (sourceGuesses assessment.strategy).expect fun decision =>
          (sourceDisclosures assessment.strategy bit decision).expect fun disclose =>
            reward (decisionResult bit decision disclose) bob) := by
  let alternative := (sourceProfile (FinDist.pure guess) (FinDist.pure false)) bob
  have optimal := rational bob sourceBobSite alternative (Set.mem_univ _)
  change (assessment.continuationContext sourceBobSite (sourceResultPayoff reward bob) 3).value
    alternative ≤ _ at optimal
  rw [source_result_bob_context reward assessment consistent,
    source_result_bob_context reward assessment consistent, Profile.update_eq_self] at optimal
  have chosen : sourceGuesses (Profile.update (sig := sourceModel.behavioralSignature)
      assessment.strategy bob alternative) =
      FinDist.pure guess := by
    simpa only [sourceGuesses, sourceDecisionLaw, sourceChoice, Profile.update_same,
      alternative, sourceBobSite, InformationModel.informationSite] using
        profile_guess_law (FinDist.pure guess) (FinDist.pure false) false
  simpa only [chosen, FinDist.expect_pure] using optimal

end VegasTests.MonitoredGuessing.Restricted
