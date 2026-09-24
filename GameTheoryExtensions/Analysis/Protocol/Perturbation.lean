/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.Bayes

/-! # Common fully mixed perturbations of behavioral profiles

Mix any prescribed profile with one fully mixed reference profile. A positive
weight supplies every legal choice, and weights tending to zero recover every
prescribed strategy coordinate. Bayes normalization then supplies the beliefs
of each approximant. In finite protocols, `ConsistencyCompletion` extracts a
common subsequence with convergent beliefs. Strategy convergence alone does
not determine posteriors at off-path information sets or their incentives.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type} {E : ExecutionProtocol ι} {M : InformationModel E}

def BehavioralAssessment.perturb (reference : M.BehavioralAssessment)
    (profile : ∀ who, M.BehavioralPolicy who) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) : M.BehavioralAssessment :=
  BehavioralAssessment.ofStrategy fun who info =>
    FinDist.mix weight nonnegative atMostOne (reference.strategy who info) (profile who info)

theorem BehavioralAssessment.perturb_fullyMixed (reference : M.BehavioralAssessment)
    (mixed : reference.IsFullyMixed) (profile : ∀ who, M.BehavioralPolicy who) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (positive : 0 < weight) :
    (reference.perturb profile weight nonnegative atMostOne).IsFullyMixed := by
  intro who site choice
  exact FinDist.mem_support_mix_left weight nonnegative atMostOne positive
    (mixed who site choice)

theorem BehavioralAssessment.perturb_strategy_converges (reference : M.BehavioralAssessment)
    (profile : ∀ who, M.BehavioralPolicy who) (weight : Nat → ℝ)
    (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) (who : ι) (info : M.InfoState who) :
    FinDistConvergesPointwise
      (fun n => (reference.perturb profile (weight n) (nonnegative n)
        (atMostOne n)).strategy who info) (profile who info) := by
  intro choice
  change Tendsto (fun n => (FinDist.mix (weight n) (nonnegative n) (atMostOne n)
    (reference.strategy who info) (profile who info)).prob choice) atTop _
  simp only [FinDist.prob_mix]
  have first := vanishes.mul_const ((reference.strategy who info).prob choice)
  have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have second := (one.sub vanishes).mul_const ((profile who info).prob choice)
  simpa only [zero_mul, sub_zero, one_mul, zero_add] using first.add second

end GameTheory.Protocol.InformationModel
