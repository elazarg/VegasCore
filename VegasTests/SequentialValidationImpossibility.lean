/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationNativeIncentives
import VegasTests.SequentialValidationEquilibrium

/-! # Authenticated disclosure prevents utility-independent sequential compilation

The same actual source assessment is a sequential equilibrium for opposite
guessing utilities. No common native behavioral profile admits sequentially
rational assessments for both, even with different off-path beliefs. The
native game uses the bounded packet menu and authorized at-most-once service.
This is a preservation obstruction, not nonexistence of native equilibria.
-/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativeGuessPolicy (guess : Bool) : nativeModel.BehavioralPolicy true := fun info =>
  match info with
  | none => FinDist.pure ⟨none, rfl⟩
  | some (past, view) => FinDist.pure
      ⟨some ⟨some (.submit (nativeGuessSubmission guess))⟩,
        ⟨_, native_guess_available guess past view, rfl⟩⟩

theorem native_guess_deviation (profile : Profile nativeModel.behavioralSignature)
    (bit guess : Bool) :
    nativeGuessLaw (Profile.update (sig := nativeModel.behavioralSignature)
      profile true (nativeGuessPolicy guess)) bit = FinDist.pure guess := by
  simp only [nativeGuessLaw, nativePlayers, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    Profile.update, Function.update_self, nativeGuessPolicy, FinDist.map_pure, FinDist.pure_bind]
  exact native_tail_guess bit guess

theorem native_continuation_value (assessment : nativeModel.BehavioralAssessment)
    (matchBit bit : Bool) (alternative : nativeModel.BehavioralPolicy true) :
    (assessment.continuationContext (nativeBobSite bit) (nativePayoff matchBit true) 113).value
      alternative =
        (nativeGuessLaw (Profile.update (sig := nativeModel.behavioralSignature)
          assessment.strategy true alternative) bit).expect
            (fun guess => if (guess == bit) = matchBit then (1 : ℝ) else 0) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  calc
    _ = (assessment.belief true (nativeBobSite bit)).expect (fun _ =>
          (nativeGuessLaw (Profile.update (sig := nativeModel.behavioralSignature)
            assessment.strategy true alternative) bit).expect
              (fun guess => if (guess == bit) = matchBit then (1 : ℝ) else 0)) := by
      apply FinDist.expect_congr
      intro history _
      exact native_bob_value _ matchBit bit history
    _ = _ := FinDist.expect_const _ _

theorem native_rational_payoff_one (assessment : nativeModel.BehavioralAssessment)
    (matchBit : Bool)
    (rational : assessment.IsSequentiallyRationalWithin (nativePayoff matchBit) 113) :
    1 ≤ (nativeGuessLaw assessment.strategy false).expect
      (fun guess => if (guess == false) = matchBit then (1 : ℝ) else 0) := by
  have inequality := rational true (nativeBobSite false) (nativeGuessPolicy (!matchBit))
    (Set.mem_univ _)
  change (assessment.continuationContext (nativeBobSite false)
      (nativePayoff matchBit true) 113).value
      (nativeGuessPolicy (!matchBit)) ≤
    (assessment.continuationContext (nativeBobSite false) (nativePayoff matchBit true) 113).value
      (assessment.strategy true) at inequality
  rw [native_continuation_value, native_continuation_value, native_guess_deviation,
    FinDist.expect_pure, Profile.update_eq_self] at inequality
  cases matchBit <;> simpa using inequality

/-- Hidden histories and utility-dependent beliefs cannot rationalize the
same native behavior for the two opposite guessing objectives. -/
theorem native_no_common_rational_strategy : ¬ ∃ first second : nativeModel.BehavioralAssessment,
    first.strategy = second.strategy ∧
      first.IsSequentiallyRationalWithin (nativePayoff true) 113 ∧
      second.IsSequentiallyRationalWithin (nativePayoff false) 113 := by
  rintro ⟨first, second, same, firstRational, secondRational⟩
  have matchOptimal := native_rational_payoff_one first true firstRational
  have mismatchOptimal := native_rational_payoff_one second false secondRational
  rw [← same] at mismatchOptimal
  have total :
      (nativeGuessLaw first.strategy false).expect
          (fun guess => if (guess == false) = true then (1 : ℝ) else 0) +
        (nativeGuessLaw first.strategy false).expect
          (fun guess => if (guess == false) = false then (1 : ℝ) else 0) = 1 := by
    rw [← FinDist.expect_add]
    calc
      _ = (nativeGuessLaw first.strategy false).expect (fun _ => (1 : ℝ)) := by
        apply FinDist.expect_congr
        intro guess _
        cases guess <;> norm_num
      _ = _ := FinDist.expect_const _ _
  linarith

/-- Even a whole-profile translator cannot preserve both source equilibria
without inspecting which utility is being analyzed. Beliefs may be translated
differently for each utility. All deviations use the actual native response menu. -/
theorem native_no_utility_independent_sequential_translation : ¬ ∃ translate :
    Profile sourceModel.behavioralSignature → Profile nativeModel.behavioralSignature,
    ∀ matchBit,
      sourceAssessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
        sourceAssessment.continuationContext site (sourcePayoff matchBit who) 5) →
      ∃ target : nativeModel.BehavioralAssessment,
        target.strategy = translate sourceAssessment.strategy ∧
          target.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
            target.continuationContext site (nativePayoff matchBit who) 113) := by
  rintro ⟨translate, preserves⟩
  obtain ⟨first, firstEq, firstEquilibrium⟩ := preserves true (source_sequential_equilibrium true)
  obtain ⟨second, secondEq, secondEquilibrium⟩ :=
    preserves false (source_sequential_equilibrium false)
  exact native_no_common_rational_strategy ⟨first, second, firstEq.trans secondEq.symm,
    firstEquilibrium.1, secondEquilibrium.1⟩

end VegasTests.SequentialValidation
