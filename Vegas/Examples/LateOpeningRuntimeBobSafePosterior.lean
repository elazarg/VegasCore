/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSuccessPosterior

/-! # Native posterior restrictions from a supported Safe answer

At an actual timely binding after sender success, any supported response
selecting Safe forces all three private-label posterior masses into the closed
interval from one fifth to two fifths. This uses the full native information
class, its actual belief and the original raw response law.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSafePosterior

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobSuccessInformation
  LateOpeningRuntimeBobSuccessDecision LateOpeningRuntimeBobSuccessOptimization
  LateOpeningRuntimeSuccessPosterior LateOpeningRuntimeBindingPosterior
open LateOpeningRuntimeBobRawBinding (serviced)
open LateOpeningRuntimeBobBindingDecision (context)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)

theorem label_mass_sum
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (∑ label : Fin 3,
      labelMass weight nonnegative site representative decision current assessment label) = 1 := by
  classical
  unfold labelMass
  rw [← expect_sum _ _ (fun _ => payoffIntegrable_ite_one_zero _ _)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  exact expect_constant _ 1

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

include representative current in
theorem supported_safe_label_bounds
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support)
    (selected : (serviced decision.execution response).application.config.store
      (.inr bobBindEvent) = some (.success safe)) (label : Fin 3) :
    (1 / 5 : ℝ) ≤
      readoutBelief weight nonnegative site assessment initializedLabel (some label) ∧
    readoutBelief weight nonnegative site assessment initializedLabel (some label) ≤ 2 / 5 := by
  obtain ⟨answer, binding, _shape, maximizing⟩ := rational_supported_binding weight nonnegative
    site representative decision current reward forfeit deposit forfeitNonnegative
      depositNonnegative assessment rational response supported
  have same : answer = safe := by
    exact (PublicationResult.success.inj (Option.some.inj (selected.symm.trans binding))).symm
  subst answer
  rw [safe_context_value weight nonnegative site representative decision current] at maximizing
  have upper (other : Fin 3) :
      labelMass weight nonnegative site representative decision current assessment other ≤ 2 / 5 :=
    by
    rw [← label_guess_context_value weight nonnegative site representative decision current
      reward forfeit deposit]
    exact (answer_value_le_bestAnswerValue weight nonnegative site representative decision current
      reward forfeit deposit assessment (labelGuess other)).trans_eq maximizing.symm
  have partition := label_mass_sum weight nonnegative site representative decision current
    assessment
  rw [Fin.sum_univ_three] at partition
  rw [← label_mass_eq_readout weight nonnegative site representative decision current]
  constructor
  · have lowerZero : (1 / 5 : ℝ) ≤
        labelMass weight nonnegative site representative decision current assessment 0 := by
      linarith [upper 1, upper 2]
    have lowerOne : (1 / 5 : ℝ) ≤
        labelMass weight nonnegative site representative decision current assessment 1 := by
      linarith [upper 0, upper 2]
    have lowerTwo : (1 / 5 : ℝ) ≤
        labelMass weight nonnegative site representative decision current assessment 2 := by
      linarith [upper 0, upper 1]
    fin_cases label
    · exact lowerZero
    · exact lowerOne
    · exact lowerTwo
  · exact upper label

end Vegas.Examples.LateOpeningRuntimeBobSafePosterior
