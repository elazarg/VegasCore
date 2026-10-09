/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSafePosterior
import Vegas.Examples.LateOpeningRuntimeAliceSuccessfulReduction
import Vegas.Examples.LateOpeningRuntimeFirstRetryComparison

/-! # Native Safe probabilities and label posterior restrictions

A positive typed Safe atom lifts to a supported original raw response at
the actual successful receiver decision. Rationality therefore bounds every
actual private-label posterior between one fifth and two fifths. If a pair
of successful information classes has positive Safe atoms, every cross-label
posterior product is at least one twenty-fifth. A zero product therefore
excludes positive Safe atoms at both classes.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSafeProbability

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobSuccessInformation
  LateOpeningRuntimeBindingPosterior LateOpeningRuntimeSuccessPosterior
open LateOpeningRuntimeAliceFailureReduction (bindingLaw)
open LateOpeningRuntimeAliceSuccessfulReduction (safeProbability successful_binding_law)
open LateOpeningRuntimeBobBindingDecision (context)
open LateOpeningRuntimeBobSuccessOptimization (currentResponses)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def bindingSafeProbability
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (execution : app.Execution) : ℝ :=
  ((bindingLaw (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative profile)
    execution) (some (.success safe))).toReal

theorem bindingSafeProbability_nonnegative
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (execution : app.Execution) : 0 ≤ bindingSafeProbability weight nonnegative profile execution :=
  ENNReal.toReal_nonneg

section SuccessfulSite

variable (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

include representative current in
/-- The actual typed Safe atom is a sum over the original raw responses,
so a positive atom supplies a supported response selecting Safe. -/
theorem positive_safe_label_bounds
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (positive : 0 < bindingSafeProbability weight nonnegative assessment.strategy
      decision.execution) (label : Fin 3) :
    (1 / 5 : ℝ) ≤ readoutBelief weight nonnegative site assessment initializedLabel (some label) ∧
      readoutBelief weight nonnegative site assessment initializedLabel (some label) ≤ 2 / 5 := by
  have nonzero : ((bindingLaw
      (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative assessment.strategy)
      decision.execution) (some (.success safe))) ≠ 0 := by
    intro zero
    have impossible : bindingSafeProbability weight nonnegative assessment.strategy
        decision.execution = 0 := by
      rw [bindingSafeProbability, zero, ENNReal.toReal_zero]
    linarith
  have supported : some (.success safe) ∈ (bindingLaw
      (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative assessment.strategy)
        decision.execution).support := (PMF.mem_support_iff _ _).mpr nonzero
  unfold bindingLaw at supported
  obtain ⟨response, responseSupported, selected⟩ := PMF.support_map .. ▸ supported
  exact LateOpeningRuntimeBobSafePosterior.supported_safe_label_bounds weight nonnegative
    site representative decision current reward forfeit deposit forfeitNonnegative
      depositNonnegative assessment rational response responseSupported selected label

include representative current in
/-- Global rationality uses the original native continuation context;
bounded execution identifies it with the checked finite context. -/
theorem rational_positive_safe_label_bounds
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (positive : 0 < bindingSafeProbability weight nonnegative assessment.strategy
      decision.execution) (label : Fin 3) :
    (1 / 5 : ℝ) ≤ readoutBelief weight nonnegative site assessment initializedLabel (some label) ∧
      readoutBelief weight nonnegative site assessment initializedLabel (some label) ≤ 2 / 5 := by
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact positive_safe_label_bounds weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment localRational
      positive label

end SuccessfulSite

/-- If both actual typed Safe atoms are positive, every cross-label
posterior product has the quantitative lower bound one twenty-fifth. -/
theorem positive_safe_label_product_lower_bound
    (firstSite secondSite : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (firstRepresentative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob firstSite.1)
    (secondRepresentative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob secondSite.1)
    (firstDecision secondDecision : DecisionHistory weight nonnegative)
    (firstCurrent : firstRepresentative.1.state = some ⟨14, some bob, firstDecision.execution⟩)
    (secondCurrent : secondRepresentative.1.state = some ⟨14, some bob, secondDecision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (firstPositive : 0 < bindingSafeProbability weight nonnegative assessment.strategy
      firstDecision.execution)
    (secondPositive : 0 < bindingSafeProbability weight nonnegative assessment.strategy
      secondDecision.execution) (firstLabel secondLabel : Fin 3) :
    (1 / 25 : ℝ) ≤
      readoutBelief weight nonnegative firstSite assessment initializedLabel (some firstLabel) *
        readoutBelief weight nonnegative secondSite assessment initializedLabel
          (some secondLabel) := by
  have firstLower := (rational_positive_safe_label_bounds weight nonnegative firstSite
    firstRepresentative firstDecision firstCurrent reward forfeit deposit forfeitNonnegative
      depositNonnegative assessment rational firstPositive firstLabel).1
  have secondLower := (rational_positive_safe_label_bounds weight nonnegative secondSite
    secondRepresentative secondDecision secondCurrent reward forfeit deposit forfeitNonnegative
      depositNonnegative assessment rational secondPositive secondLabel).1
  calc
    (1 / 25 : ℝ) = (1 / 5 : ℝ) * (1 / 5) := by norm_num
    _ ≤ _ := mul_le_mul firstLower secondLower (by norm_num) (by linarith)

/-- No beliefs or reach probabilities are prescribed: the cross product
concerns the supplied assessment's full actual information classes. -/
theorem safe_zero_of_label_product_zero
    (firstSite secondSite : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (firstRepresentative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob firstSite.1)
    (secondRepresentative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob secondSite.1)
    (firstDecision secondDecision : DecisionHistory weight nonnegative)
    (firstCurrent : firstRepresentative.1.state = some ⟨14, some bob, firstDecision.execution⟩)
    (secondCurrent : secondRepresentative.1.state = some ⟨14, some bob, secondDecision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (firstLabel secondLabel : Fin 3)
    (productZero : readoutBelief weight nonnegative firstSite assessment initializedLabel
        (some firstLabel) * readoutBelief weight nonnegative secondSite assessment initializedLabel
          (some secondLabel) = 0) :
    bindingSafeProbability weight nonnegative assessment.strategy firstDecision.execution = 0 ∨
      bindingSafeProbability weight nonnegative assessment.strategy secondDecision.execution = 0 :=
    by
  by_cases firstZero :
      bindingSafeProbability weight nonnegative assessment.strategy firstDecision.execution = 0
  · exact Or.inl firstZero
  right
  by_contra secondNonzero
  have firstPositive :
      0 < bindingSafeProbability weight nonnegative assessment.strategy firstDecision.execution :=
    (bindingSafeProbability_nonnegative weight nonnegative assessment.strategy
      firstDecision.execution).lt_of_ne' firstZero
  have secondPositive :
      0 < bindingSafeProbability weight nonnegative assessment.strategy secondDecision.execution :=
    (bindingSafeProbability_nonnegative weight nonnegative assessment.strategy
      secondDecision.execution).lt_of_ne' secondNonzero
  have lower := positive_safe_label_product_lower_bound weight nonnegative firstSite secondSite
    firstRepresentative secondRepresentative firstDecision secondDecision firstCurrent secondCurrent
      reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational
        firstPositive secondPositive firstLabel secondLabel
  rw [productZero] at lower
  norm_num at lower

theorem canonical_bindingSafeProbability (positive : 0 < weight)
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) :
    bindingSafeProbability weight nonnegative profile
      (LateOpeningRuntimeLateAcceptance.answerDecision bit label slot seen) =
      safeProbability (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative profile)
        bit seen := by
  unfold bindingSafeProbability
  rw [successful_binding_law weight nonnegative positive
    (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative profile)
      bit label slot seen samplePossible]
  rfl

/-- This form directly uses the native canonical accepted-opening
representatives, while retaining their arbitrary private labels and raw policy. -/
theorem rational_positive_safeProbability_label_bounds (positive : 0 < weight)
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1) (bit : Bool) (privateLabel : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false)
    (current : representative.1.state = some ⟨14, some bob,
      LateOpeningRuntimeLateAcceptance.answerDecision bit privateLabel slot seen⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (safePositive : 0 < safeProbability
      (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative assessment.strategy)
        bit seen) (label : Fin 3) :
    (1 / 5 : ℝ) ≤ readoutBelief weight nonnegative site assessment initializedLabel (some label) ∧
      readoutBelief weight nonnegative site assessment initializedLabel (some label) ≤ 2 / 5 := by
  apply rational_positive_safe_label_bounds weight nonnegative site representative
    (LateOpeningRuntimeAliceSuccessfulContinuation.decisionHistory weight nonnegative positive
      bit privateLabel slot seen samplePossible) current reward forfeit deposit forfeitNonnegative
        depositNonnegative assessment rational _ label
  change 0 < bindingSafeProbability weight nonnegative assessment.strategy
    (LateOpeningRuntimeLateAcceptance.answerDecision bit privateLabel slot seen)
  rw [canonical_bindingSafeProbability weight nonnegative positive assessment.strategy
    bit privateLabel slot seen samplePossible]
  exact safePositive

theorem safeProbability_zero_of_label_product_zero (positive : 0 < weight)
    (firstSite secondSite : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (firstRepresentative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob firstSite.1)
    (secondRepresentative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob secondSite.1) (bit : Bool) (firstPrivateLabel secondPrivateLabel : Fin 3)
    (firstCurrent : firstRepresentative.1.state = some ⟨14, some bob,
      LateOpeningRuntimeLateAcceptance.answerDecision bit firstPrivateLabel 0 true⟩)
    (secondCurrent : secondRepresentative.1.state = some ⟨14, some bob,
      LateOpeningRuntimeLateAcceptance.answerDecision bit secondPrivateLabel 0 false⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (firstLabel secondLabel : Fin 3)
    (productZero : readoutBelief weight nonnegative firstSite assessment initializedLabel
        (some firstLabel) * readoutBelief weight nonnegative secondSite assessment initializedLabel
          (some secondLabel) = 0) :
    safeProbability (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative
      assessment.strategy) bit true = 0 ∨
    safeProbability (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative
      assessment.strategy) bit false = 0 := by
  have disjunction := safe_zero_of_label_product_zero weight nonnegative firstSite secondSite
    firstRepresentative secondRepresentative
    (LateOpeningRuntimeAliceSuccessfulContinuation.decisionHistory weight nonnegative positive
      bit firstPrivateLabel 0 true (Or.inl rfl))
    (LateOpeningRuntimeAliceSuccessfulContinuation.decisionHistory weight nonnegative positive
      bit secondPrivateLabel 0 false (Or.inl rfl)) firstCurrent secondCurrent reward forfeit deposit
        forfeitNonnegative depositNonnegative assessment rational firstLabel secondLabel productZero
  change bindingSafeProbability weight nonnegative assessment.strategy
      (LateOpeningRuntimeLateAcceptance.answerDecision bit firstPrivateLabel 0 true) = 0 ∨
    bindingSafeProbability weight nonnegative assessment.strategy
      (LateOpeningRuntimeLateAcceptance.answerDecision bit secondPrivateLabel 0 false) = 0
    at disjunction
  rw [canonical_bindingSafeProbability weight nonnegative positive assessment.strategy
    bit firstPrivateLabel 0 true (Or.inl rfl),
    canonical_bindingSafeProbability weight nonnegative positive assessment.strategy
      bit secondPrivateLabel 0 false (Or.inl rfl)] at disjunction
  exact disjunction

end Vegas.Examples.LateOpeningRuntimeBobSafeProbability
