/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationIncentives

/-! # One source sequential equilibrium for opposite guessing utilities -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem source_failed_pair (profile : Profile sourceModel.behavioralSignature)
    (matchBit : Bool) (site : sourceModel.InformationSite true)
    (failed : sourceSecretResult site.1 = .failure)
    (history : sourceModel.InformationHistory true site.1) :
    (sourceModel.runBehavioralFrom profile 5 history.1).expect (sourcePayoff matchBit true) +
      (sourceModel.runBehavioralFrom profile 5 (sourceFlip site failed history).1).expect
        (sourcePayoff matchBit true) = 1 := by
  obtain ⟨bit, dummy, first, second, same⟩ := source_bob_history site history
  have flag : ((first && dummy.isSuccess) || !second) = true := by
    have result := congrArg sourceSecretResult history.2
    rw [same, source_secret_info, failed] at result
    split at result
    · assumption
    · cases result
  have infoEq : (sourceBobSite (!bit) dummy first second).1 =
      (sourceBobSite bit dummy first second).1 :=
    secret_bob_info (!bit) bit dummy first second flag
  change _ + (sourceModel.runBehavioralFrom profile 5 (flipSourceHistory history.1)).expect _ = _
  rw [same, flipSourceHistory_path]
  change _ + (sourceModel.runBehavioralFrom profile 5
    (SourcePath.secretPublished (!bit) dummy first second).history).expect _ = _
  rw [source_bob_value, source_bob_value, infoEq]
  simp only [flag, ↓reduceIte]
  exact source_guess_pair _ matchBit bit

theorem source_success_value (profile : Profile sourceModel.behavioralSignature)
    (matchBit : Bool) (site : sourceModel.InformationSite true)
    (succeeded : sourceSecretResult site.1 ≠ .failure)
    (history : sourceModel.InformationHistory true site.1) :
    (sourceModel.runBehavioralFrom profile 5 history.1).expect (sourcePayoff matchBit true) = 0 :=
  by
    obtain ⟨bit, dummy, first, second, same⟩ := source_bob_history site history
    have flag : ((first && dummy.isSuccess) || !second) = false := by
      have result := congrArg sourceSecretResult history.2
      rw [same, source_secret_info] at result
      cases flag : (first && dummy.isSuccess) || !second
      · rfl
      · simp only [flag, ↓reduceIte] at result
        exact (succeeded result.symm).elim
    rw [same, source_bob_value]
    simp only [flag, Bool.false_eq_true, ↓reduceIte, FinDist.expect_const]

theorem source_guessing_value (matchBit : Bool) (site : sourceModel.InformationSite true)
    (alternative : sourceModel.BehavioralPolicy true) :
    (sourceAssessment.continuationContext site (sourcePayoff matchBit true) 5).value alternative =
      if sourceSecretResult site.1 = .failure then 1 / 2 else 0 := by
  classical
  rw [InformationModel.BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  let profile := Profile.update (sig := sourceModel.behavioralSignature)
    sourceAssessment.strategy true alternative
  let value := fun (history : sourceModel.InformationHistory true site.1) =>
    (sourceModel.runBehavioralFrom profile 5 history.1).expect (sourcePayoff matchBit true)
  change (sourceAssessment.belief true site).expect value = _
  by_cases failed : sourceSecretResult site.1 = .failure
  · rw [ite_eq_left failed]
    have symmetric : (sourceAssessment.belief true site).expect
        (fun history => value (sourceFlip site failed history)) =
        (sourceAssessment.belief true site).expect value := by
      rw [← FinDist.expect_map, source_belief_flip]
    have sum : (sourceAssessment.belief true site).expect value +
        (sourceAssessment.belief true site).expect
          (fun history => value (sourceFlip site failed history)) = 1 := by
      rw [← FinDist.expect_add]
      calc
        _ = (sourceAssessment.belief true site).expect (fun _ => (1 : ℝ)) := by
          apply FinDist.expect_congr
          intro history _
          exact source_failed_pair profile matchBit site failed history
        _ = _ := FinDist.expect_const _ _
    linarith
  · rw [ite_eq_right failed]
    calc
      _ = (sourceAssessment.belief true site).expect (fun _ => (0 : ℝ)) := by
        apply FinDist.expect_congr
        intro history _
        exact source_success_value profile matchBit site failed history
      _ = _ := FinDist.expect_const _ _

theorem source_alice_zero (matchBit : Bool) (history : sourceArena.History) :
    sourcePayoff matchBit false history = 0 := by
  unfold sourcePayoff
  rcases history.state with _ | config | config | config | config | config <;> rfl

theorem source_rational (matchBit : Bool) :
    sourceAssessment.IsSequentiallyRationalWithin (sourcePayoff matchBit) 5 := by
  intro who site alternative _
  cases who
  · have zero : sourcePayoff matchBit false = fun _ => 0 :=
      funext (source_alice_zero matchBit)
    change (sourceAssessment.continuationContext site (sourcePayoff matchBit false) 5).value
      alternative ≤ _
    rw [zero]
    simp [InformationModel.BehavioralAssessment.continuationContext, Context.value, zero]
  · change (sourceAssessment.continuationContext site (sourcePayoff matchBit true) 5).value
      alternative ≤ _
    rw [source_guessing_value, source_guessing_value]

/-- The full forfeiture interface has one fully mixed sequential equilibrium
for both matching and mismatching the private type after publication failure. -/
theorem source_sequential_equilibrium (matchBit : Bool) :
    sourceAssessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      sourceAssessment.continuationContext site (sourcePayoff matchBit who) 5) :=
  ⟨source_rational matchBit, source_consistent⟩

end VegasTests.SequentialValidation
