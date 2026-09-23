/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment
import GameTheoryExtensions.Core.IncentiveCone

/-! # Incentive comparisons at information sets

The assessment supplies beliefs over complete histories. Deviations replace a
player's whole continuation policy and retain those beliefs and all opponents.
For fixed assessments and finite observed outcomes, cone inclusion exactly
characterizes preservation of sequential rationality for every utility profile.
Belief consistency is a separate obligation; no subgame roots are used here.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} (M : InformationModel E)

abbrev AssessmentDeviation (who : ι) := M.InformationSite who × M.BehavioralPolicy who

def assessmentComparison {Observation : Type*} (observe : E.History → Observation)
    (fuel : Nat) (assessment : M.BehavioralAssessment) (who : ι)
    (deviation : M.AssessmentDeviation who) : IncentiveComparison Observation where
  prescribed := ((assessment.continuationContext deviation.1 (fun _ => 0) fuel).outcome
    (assessment.strategy who)).map observe
  alternative := ((assessment.continuationContext deviation.1 (fun _ => 0) fuel).outcome
    deviation.2).map observe

theorem isSequentiallyRationalWithin_iff_comparisons
    {Observation : Type*} (observe : E.History → Observation) (fuel : Nat)
    (assessment : M.BehavioralAssessment) (utility : Observation → ι → ℝ) :
    assessment.IsSequentiallyRationalWithin (fun who history => utility (observe history) who)
        fuel ↔
      ∀ who deviation, (M.assessmentComparison observe fuel assessment who deviation).Holds
        (utility · who) := by
  constructor
  · intro rational who ⟨site, alternative⟩
    simpa only [assessmentComparison, IncentiveComparison.Holds, FinDist.expect_map,
      Context.value, BehavioralAssessment.continuationContext] using
      rational who site alternative (Set.mem_univ _)
  · intro respected who site alternative _
    simpa only [assessmentComparison, IncentiveComparison.Holds, FinDist.expect_map,
      Context.value, BehavioralAssessment.continuationContext] using
      respected who (site, alternative)

variable {T : ExecutionProtocol ι} (N : InformationModel T)

/-- Exact incentive transport for fixed strategy/belief pairs. This theorem
does not assert that either belief system is sequentially consistent. -/
theorem sequential_rationality_preservation_iff_cone
    {Observation : Type*} [Fintype Observation]
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    (sourceFuel targetFuel : Nat)
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment) :
    (∀ utility : Observation → ι → ℝ,
      source.IsSequentiallyRationalWithin
        (fun who history => utility (sourceObserve history) who) sourceFuel →
      target.IsSequentiallyRationalWithin
        (fun who history => utility (targetObserve history) who) targetFuel) ↔
    ∀ who (deviation : N.AssessmentDeviation who),
      (N.assessmentComparison targetObserve targetFuel target who deviation).difference ∈
        IncentiveComparison.cone (M.assessmentComparison sourceObserve sourceFuel source who) := by
  simp only [M.isSequentiallyRationalWithin_iff_comparisons sourceObserve sourceFuel,
    N.isSequentiallyRationalWithin_iff_comparisons targetObserve targetFuel]
  constructor
  · intro preserves who deviation
    rw [IncentiveComparison.mem_cone_iff]
    intro utility respected
    let utilities : Observation → ι → ℝ := fun outcome player =>
      if player = who then utility outcome else 0
    have sourceRespects : ∀ player replacement,
        (M.assessmentComparison sourceObserve sourceFuel source player replacement).Holds
          (utilities · player) := by
      intro player replacement
      by_cases same : player = who
      · subst player
        simpa only [utilities, ↓reduceIte] using respected replacement
      · simp only [IncentiveComparison.Holds, utilities, same, ↓reduceIte,
          FinDist.expect_const, le_refl]
    simpa only [utilities, ↓reduceIte] using preserves utilities sourceRespects who deviation
  · intro included utility sourceRespects who deviation
    exact (IncentiveComparison.mem_cone_iff _ _).mp (included who deviation)
      (utility · who) (sourceRespects who)

end GameTheory.Protocol.InformationModel
