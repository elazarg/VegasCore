/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Math.Probability.ExpectationAlgebra

/-! # Linear utility closure for one sequential assessment

One fixed assessment and continuation runner remain rational for nonnegative
playerwise linear combinations of utilities for which that assessment is
rational. Finite histories supply integrability; its consistency witness is
unchanged. The result does not combine different equilibrium assessments.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.BehavioralAssessment

open GameTheory.Math.Probability

variable {ι : Type*} {E : ExecutionProtocol ι} {M : InformationModel E}

/-- Nonnegative playerwise linear combinations preserve the rationality of one
assessment for one continuation runner. -/
theorem isSequentiallyRationalWith_nonnegative_linear [DecidableEq ι] [Finite E.History]
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    (first second : ι → E.History → ℝ) (left right : ι → ℝ)
    (left_nonnegative : ∀ who, 0 ≤ left who)
    (right_nonnegative : ∀ who, 0 ≤ right who)
    (first_rational : assessment.IsSequentiallyRationalWith run first)
    (second_rational : assessment.IsSequentiallyRationalWith run second) :
    assessment.IsSequentiallyRationalWith run
      (fun who history => left who * first who history + right who * second who history) := by
  intro who site
  let firstContext := assessment.continuationContextWith run site (first who)
  let secondContext := assessment.continuationContextWith run site (second who)
  let combinedContext := assessment.continuationContextWith run site
    (fun history => left who * first who history + right who * second who history)
  have integrable (context : GameTheory.Protocol.Context (M.BehavioralPolicy who) E.History)
      (alternative : M.BehavioralPolicy who) : context.IntegrableAt alternative :=
    payoffIntegrable_of_finite _ _
  have combined_value (alternative : M.BehavioralPolicy who) :
      combinedContext.value alternative = left who * firstContext.value alternative +
        right who * secondContext.value alternative := by
    change expect (firstContext.outcome alternative)
      (fun history => left who * first who history + right who * second who history) = _
    rw [expect_add
      (payoffIntegrable_const_mul (payoffIntegrable_of_finite _ _))
      (payoffIntegrable_const_mul (payoffIntegrable_of_finite _ _)),
      expect_const_mul, expect_const_mul]
    rfl
  apply (GameTheory.Protocol.Context.isLocallyOptimal_iff_of_integrable
    (integrable combinedContext _) (fun alternative _ => integrable combinedContext alternative)).2
  intro alternative allowed
  have first_optimal :=
    (GameTheory.Protocol.Context.isLocallyOptimal_iff_of_integrable
      (integrable firstContext _) (fun option _ => integrable firstContext option)).1
      (first_rational who site) alternative allowed
  have second_optimal :=
    (GameTheory.Protocol.Context.isLocallyOptimal_iff_of_integrable
      (integrable secondContext _) (fun option _ => integrable secondContext option)).1
      (second_rational who site) alternative allowed
  rw [combined_value, combined_value]
  exact add_le_add (mul_le_mul_of_nonneg_left first_optimal (left_nonnegative who))
    (mul_le_mul_of_nonneg_left second_optimal (right_nonnegative who))

/-- The same consistent assessment is an equilibrium for every nonnegative
linear combination of two utilities for which it is already an equilibrium. -/
theorem isSequentialEquilibriumFor_nonnegative_linear [Fintype ι] [DecidableEq ι]
    [Finite E.History] (assessment : M.BehavioralAssessment)
    (antichain : M.DecisionInformationAntichain) (run : M.ContinuationRunner)
    (first second : ι → E.History → ℝ) (left right : ι → ℝ)
    (left_nonnegative : ∀ who, 0 ≤ left who)
    (right_nonnegative : ∀ who, 0 ≤ right who)
    (first_equilibrium : assessment.IsSequentialEquilibriumFor antichain
      (fun who site => assessment.continuationContextWith run site (first who)))
    (second_equilibrium : assessment.IsSequentialEquilibriumFor antichain
      (fun who site => assessment.continuationContextWith run site (second who))) :
    assessment.IsSequentialEquilibriumFor antichain
      (fun who site => assessment.continuationContextWith run site
        (fun history => left who * first who history + right who * second who history)) :=
  ⟨assessment.isSequentiallyRationalWith_nonnegative_linear run first second left right
    left_nonnegative right_nonnegative first_equilibrium.1 second_equilibrium.1,
    first_equilibrium.2⟩

end GameTheory.Protocol.InformationModel.BehavioralAssessment

