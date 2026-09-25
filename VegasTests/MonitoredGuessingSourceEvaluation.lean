/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingSourceInformation

/-! # Exact continuation utilities of the source guessing game -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def sourceUtility : sourceArena.State → Player → ℝ
  | some (.inr (.inr config)), who => utility (sourceResults config.state) who
  | _, _ => 0

def sourcePayoff (who : Player) (history : sourceArena.History) : ℝ :=
  sourceUtility history.state who

def Opens (profile : Profile sourceModel.behavioralSignature) : Prop :=
  ∀ bit guess, sourceDecisionLaw profile alice (sourceAliceSite bit guess).1 = FinDist.pure true

theorem sourceProfile_opens (guess : FinDist Bool) :
    Opens (sourceProfile guess (FinDist.pure true)) := fun bit decision =>
  profile_opening_law guess (FinDist.pure true) bit decision

theorem source_alice_run (profile : Profile sourceModel.behavioralSignature)
    (bit guess : Bool) :
    (sourceModel.runBehavioralFrom profile 3 (SourcePath.guessed bit guess).history).map
      History.state =
      (sourceDecisionLaw profile alice (sourceAliceSite bit guess).1).map
        (fun disclose => (SourcePath.done bit guess disclose).state) := by
  rw [source_run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    SourcePath.history_state, SourcePath.state, sourceKernel, FinDist.pure_bind,
    FinDist.bind_map, FinDist.bind_bind, sourceDecisionLaw, FinDist.map_comp]
  rw [← FinDist.map_eq_bind]
  simp only [sourceAliceSite, InformationModel.informationSite, source_info]
  rfl

theorem source_bob_run (profile : Profile sourceModel.behavioralSignature) (bit : Bool) :
    (sourceModel.runBehavioralFrom profile 3 (SourcePath.drawn bit).history).map History.state =
      (sourceDecisionLaw profile bob sourceBobSite.1).bind fun guess =>
        (sourceDecisionLaw profile alice (sourceAliceSite bit guess).1).map
          (fun disclose => (SourcePath.done bit guess disclose).state) := by
  have first : sourceBobSite.1 =
      sourceModel.infoOf bob (SourcePath.drawn bit).history.trace :=
    (drawn_bob_info bit false).symm
  rw [first, source_run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    SourcePath.history_state, SourcePath.state, sourceKernel, FinDist.pure_bind,
    FinDist.bind_map, FinDist.bind_bind, sourceDecisionLaw, FinDist.map_comp,
    sourceAliceSite, InformationModel.informationSite, source_info]
  rfl

theorem source_payoff_alice (bit guess disclose : Bool) :
    sourceUtility (SourcePath.done bit guess disclose).state alice =
      if disclose then (if bit = guess then 1 else 0) else -4 := by
  change correctness ((finalConfig bit guess disclose).state.get .here)
    ((guessConfig bit guess).state.get .here) -
      openingPenalty ((finalConfig bit guess disclose).state.get .here) = _
  rw [secret_publication, guess_publication]
  cases bit <;> cases guess <;> cases disclose <;>
    norm_num [correctness, openingPenalty, PublicationResult.isSuccess]

theorem source_payoff_bob (bit guess disclose : Bool) :
    sourceUtility (SourcePath.done bit guess disclose).state bob =
      if disclose && (bit == guess) then 1 else 0 := by
  change correctness ((finalConfig bit guess disclose).state.get .here)
    ((guessConfig bit guess).state.get .here) = _
  rw [secret_publication, guess_publication]
  cases bit <;> cases guess <;> cases disclose <;>
    norm_num [correctness, PublicationResult.isSuccess]

theorem source_alice_value (profile : Profile sourceModel.behavioralSignature)
    (bit guess : Bool) :
    (sourceModel.runBehavioralFrom profile 3 (SourcePath.guessed bit guess).history).expect
      (sourcePayoff alice) =
      (sourceDecisionLaw profile alice (sourceAliceSite bit guess).1).expect
        (fun disclose => if disclose then (if bit = guess then 1 else 0) else -4) := by
  have same := congrArg (fun law => law.expect (sourceUtility · alice))
    (source_alice_run profile bit guess)
  change (sourceModel.runBehavioralFrom profile 3 _).expect
    (fun history => sourceUtility history.state alice) = _
  simpa only [FinDist.expect_map, source_payoff_alice] using same

theorem source_bob_value (profile : Profile sourceModel.behavioralSignature)
    (opens : Opens profile) (bit : Bool) :
    (sourceModel.runBehavioralFrom profile 3 (SourcePath.drawn bit).history).expect
      (sourcePayoff bob) =
      (sourceDecisionLaw profile bob sourceBobSite.1).expect
        (fun guess => if bit = guess then 1 else 0) := by
  have same := congrArg (fun law => law.expect (sourceUtility · bob))
    (source_bob_run profile bit)
  simp only [FinDist.expect_map, FinDist.expect_bind] at same
  unfold sourcePayoff
  rw [same]
  apply FinDist.expect_congr
  intro guess _
  rw [opens, FinDist.expect_pure, source_payoff_bob]
  cases bit <;> cases guess <;> rfl

theorem source_alice_context (assessment : sourceModel.BehavioralAssessment)
    (bit guess : Bool) (alternative : sourceModel.BehavioralPolicy alice) :
    (assessment.continuationContext (sourceAliceSite bit guess) (sourcePayoff alice) 3).value
      alternative =
      (sourceDecisionLaw
        (Profile.update (sig := sourceModel.behavioralSignature)
          assessment.strategy alice alternative) alice (sourceAliceSite bit guess).1).expect
        (fun disclose => if disclose then (if bit = guess then 1 else 0) else -4) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  calc
    _ = (assessment.belief alice (sourceAliceSite bit guess)).expect (fun _ =>
        (sourceDecisionLaw
          (Profile.update (sig := sourceModel.behavioralSignature)
            assessment.strategy alice alternative) alice (sourceAliceSite bit guess).1).expect
          (fun disclose => if disclose then (if bit = guess then 1 else 0) else -4)) := by
      apply FinDist.expect_congr
      intro history _
      rw [source_alice_history_unique bit guess history, source_alice_value]
    _ = _ := FinDist.expect_const _ _

theorem opens_update_bob (profile : Profile sourceModel.behavioralSignature)
    (opens : Opens profile) (alternative : sourceModel.BehavioralPolicy bob) :
    Opens (Profile.update (sig := sourceModel.behavioralSignature) profile bob alternative) := by
  intro bit guess
  simpa only [sourceDecisionLaw, sourceChoice,
    Profile.update_of_ne _ _ (by decide : alice ≠ bob)] using opens bit guess

theorem source_bob_context (assessment : sourceModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent sourceAntichain)
    (opens : Opens assessment.strategy) (alternative : sourceModel.BehavioralPolicy bob) :
    (assessment.continuationContext sourceBobSite (sourcePayoff bob) 3).value alternative =
      1 / 2 := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, FinDist.expect_bind,
    source_consistent_bob assessment consistent, FinDist.expect_map]
  simp only [sourceBobHistory, source_bob_value _ (opens_update_bob _ opens alternative)]
  rw [FinDist.expect_comm]
  calc
    _ = (sourceDecisionLaw
        (Profile.update (sig := sourceModel.behavioralSignature)
          assessment.strategy bob alternative) bob sourceBobSite.1).expect (fun _ => (1 / 2 : ℝ)) :=
      by
        apply FinDist.expect_congr
        intro guess _
        simp only [FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype,
          Fintype.card_bool, Fintype.sum_bool]
        cases guess <;> norm_num
    _ = _ := FinDist.expect_const _ _

end VegasTests.MonitoredGuessing
