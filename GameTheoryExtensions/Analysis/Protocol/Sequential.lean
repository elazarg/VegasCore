/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Sequential
import GameTheoryExtensions.Protocol.SequentialIncentives
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Sequential equilibrium transport and finite-menu requirements

Reuse GameTheory's Kreps-Wilson predicate with its assessment-induced contexts.
For a consistent source assessment, uniform preservation is exactly target
consistency plus inclusion of the target incentive differences in the source
cones. This separates the analytic belief obligation from incentive transport.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type} {E : ExecutionProtocol ι} {M : InformationModel E}

/-- Finite-support fully mixed assessments require finite legal decision menus. -/
theorem BehavioralAssessment.IsFullyMixed.finite_choice
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    (who : ι) (site : M.InformationSite who) : Finite (M.Choice who site.1) :=
  (mixed who site).finite

theorem BehavioralAssessment.not_isFullyMixed_of_infinite_choice
    (assessment : M.BehavioralAssessment) (who : ι) (site : M.InformationSite who)
    [Infinite (M.Choice who site.1)] : ¬ assessment.IsFullyMixed := by
  intro mixed
  let := mixed.finite_choice who site
  exact not_finite (M.Choice who site.1)

variable [Fintype ι] [DecidableEq ι]
  {T : ExecutionProtocol ι} (N : InformationModel T)
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]
  [∀ who (site : N.InformationSite who), Fintype (N.InformationHistory who site.1)]

/-- A weakest semantic criterion for these fixed assessments, uniform over
utilities on a finite observation carrier. It is not a decision procedure or
a proof that a particular runtime supplies a consistent target assessment. -/
theorem sequential_equilibrium_preservation_iff
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    {Observation : Type*} [Fintype Observation]
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    (sourceFuel targetFuel : Nat)
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (sourceConsistent : source.IsSequentiallyConsistent sourceAntichain) :
    (∀ utility : Observation → ι → ℝ,
      source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
        source.continuationContext site (fun history => utility (sourceObserve history) who)
          sourceFuel) →
      target.IsSequentialEquilibriumFor targetAntichain (fun who site =>
        target.continuationContext site (fun history => utility (targetObserve history) who)
          targetFuel)) ↔
    target.IsSequentiallyConsistent targetAntichain ∧
      ∀ who (deviation : N.AssessmentDeviation who),
        (N.assessmentComparison targetObserve targetFuel target who deviation).difference ∈
          IncentiveComparison.cone
            (M.assessmentComparison sourceObserve sourceFuel source who) := by
  constructor
  · intro preserves
    have targetConsistent :=
      (preserves (fun _ _ => 0)
        ⟨source.isSequentiallyRationalWithin_zero sourceFuel, sourceConsistent⟩).2
    refine ⟨targetConsistent, ?_⟩
    apply (M.sequential_rationality_preservation_iff_cone N sourceObserve targetObserve
      sourceFuel targetFuel source target).mp
    intro utility rational
    exact (preserves utility ⟨rational, sourceConsistent⟩).1
  · rintro ⟨consistent, included⟩ utility ⟨rational, _⟩
    exact ⟨(M.sequential_rationality_preservation_iff_cone N sourceObserve targetObserve
      sourceFuel targetFuel source target).mpr included utility rational, consistent⟩

end GameTheory.Protocol.InformationModel
