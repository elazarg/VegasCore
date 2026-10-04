/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SequentialValidation.NativeIncentives
import Vegas.Examples.SequentialValidation.Equilibrium
import GameTheoryExtensions.Analysis.Protocol.DisclosureObstruction

/-! # Authenticated disclosure prevents utility-independent sequential compilation

The same actual source assessment is a sequential equilibrium for opposite
guessing utilities. No common native behavioral profile admits sequentially
rational assessments for both, even with different off-path beliefs. The
native game uses the bounded packet menu and authorized at-most-once service.
This is a preservation obstruction, not nonexistence of native equilibria.
-/

noncomputable section

namespace Vegas.Examples.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativeGuessPolicy (guess : Bool) : nativeModel.BehavioralPolicy true := fun info =>
  match info with
  | none => PMF.pure ⟨none, rfl⟩
  | some (past, view) => PMF.pure
      ⟨some ⟨some (nativeGuessSubmission guess)⟩,
        ⟨_, native_guess_available guess past view, rfl⟩⟩

theorem native_guess_deviation (profile : Profile nativeModel.behavioralSignature)
    (bit guess : Bool) :
    nativeGuessLaw (Profile.update (sig := nativeModel.behavioralSignature)
      profile true (nativeGuessPolicy guess)) bit = PMF.pure guess := by
  simp only [nativeGuessLaw, nativePlayers, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    Profile.update, Function.update_self, nativeGuessPolicy, PMF.pure_map, PMF.pure_bind]
  exact native_tail_guess bit guess

/-- The disclosed type fixes the guessing objective at every history Bob
considers possible. The common law is derived from the actual bounded native
continuation, and both outcomes are forced by legal native submissions. -/
def nativeDisclosedDecision :
    nativeModel.BinaryDecision nativePayoff (nativeModel.truncatedRunner 113) where
  player := true
  site := nativeBobSite false
  outcome profile := (nativeGuessLaw profile false).map (fun guess => guess == false)
  policy goal := nativeGuessPolicy (!goal)
  history_value profile goal history := by
    dsimp only [InformationModel.truncatedRunner]
    rw [native_bob_value profile goal false history, expect_map]
    rfl
  force profile goal := by
    rw [native_guess_deviation, PMF.pure_map]
    cases goal <;> rfl

theorem native_continuation_value (assessment : nativeModel.BehavioralAssessment)
    (matchBit bit : Bool) (alternative : nativeModel.BehavioralPolicy true) :
    (assessment.truncatedContinuationContext (nativeBobSite bit) (nativePayoff matchBit true)
        113).value
      alternative =
        expect (nativeGuessLaw (Profile.update (sig := nativeModel.behavioralSignature)
          assessment.strategy true alternative) bit)
            (fun guess => if (guess == bit) = matchBit then (1 : ℝ) else 0) := by
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
      expect_bind_of_finite]
  calc
    _ = expect (assessment.belief true (nativeBobSite bit)) (fun _ =>
          expect (nativeGuessLaw (Profile.update (sig := nativeModel.behavioralSignature)
            assessment.strategy true alternative) bit)
              (fun guess => if (guess == bit) = matchBit then (1 : ℝ) else 0)) := by
      apply expect_congr_on_support
      intro history _
      exact native_bob_value _ matchBit bit history
    _ = _ := expect_constant _ _

theorem native_rational_payoff_one (assessment : nativeModel.BehavioralAssessment)
    (matchBit : Bool)
    (rational : assessment.IsSequentiallyRationalFor fun who site =>
        assessment.truncatedContinuationContext site ((nativePayoff matchBit) who) 113) :
    1 ≤ expect (nativeGuessLaw assessment.strategy false)
      (fun guess => if (guess == false) = matchBit then (1 : ℝ) else 0) := by
  simpa only [nativeDisclosedDecision, expect_map, Function.comp_def] using
    nativeDisclosedDecision.rational_value assessment matchBit rational

/-- Hidden histories and utility-dependent beliefs cannot rationalize the
same native behavior for the two opposite guessing objectives. -/
theorem native_no_common_rational_strategy : ¬ ∃ first second : nativeModel.BehavioralAssessment,
    first.strategy = second.strategy ∧
      (first.IsSequentiallyRationalFor fun who site =>
          first.truncatedContinuationContext site ((nativePayoff true) who) 113) ∧
      second.IsSequentiallyRationalFor fun who site =>
          second.truncatedContinuationContext site ((nativePayoff false) who) 113 :=
  nativeDisclosedDecision.no_common_rational_strategy

/-- Even a whole-profile translator cannot preserve both source equilibria
without inspecting which utility is being analyzed. Beliefs may be translated
differently for each utility. All deviations use the actual native response menu. -/
theorem native_no_utility_independent_sequential_translation : ¬ ∃ translate :
    Profile sourceModel.behavioralSignature → Profile nativeModel.behavioralSignature,
    ∀ matchBit,
      sourceAssessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
        sourceAssessment.truncatedContinuationContext site (sourcePayoff matchBit who) 5) →
      ∃ target : nativeModel.BehavioralAssessment,
        target.strategy = translate sourceAssessment.strategy ∧
          target.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
            target.truncatedContinuationContext site (nativePayoff matchBit who) 113) :=
  nativeDisclosedDecision.no_utility_independent_sequential_translation
    sourceAssessment sourceAntichain nativeAntichain sourcePayoff (sourceModel.truncatedRunner 5)
    source_sequential_equilibrium

end Vegas.Examples.SequentialValidation
