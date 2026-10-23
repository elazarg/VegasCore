/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Sequential

/-! # Consistent beliefs from factored execution likelihoods

Finite groups of actual decision histories have Bayes probabilities equal to
their reach-weight sums divided by the site's mass. When two observation
families share the same type-dependent prefix likelihood, that prefix cancels
from a cross identity. A nonzero limiting timing factor on one side and a zero
factor on the other force one whole observation family to exclude a type.

The hypotheses concern sums of actual execution weights and convergence of
timing factors. They do not prescribe beliefs at unreached information sets.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type} [Fintype ι] {E : ExecutionProtocol ι} {M : InformationModel E}

/-- The execution likelihood of the same finite group of complete histories. -/
def finiteHistoryReach (profile : ∀ who, M.BehavioralPolicy who) (who : ι)
    (site : M.InformationSite who)
    (histories : Finset (M.InformationHistory who site.1)) : ℝ :=
  ∑ history ∈ histories, (M.historyReachWeight profile history.1).toReal

/-- An observation family with execution likelihoods factored into a shared
type prefix, a public-observation factor, and a type-dependent timing factor.
The finite groups may include multiple raw representations and retry paths. -/
structure FactoredHistoryLikelihood (who : ι) (Index Label : Type)
    (prefixLikelihood : (∀ who, M.BehavioralPolicy who) → Label → ℝ) where
  site : Index → M.InformationSite who
  histories : (index : Index) → Label → Finset (M.InformationHistory who (site index).1)
  observationFactor : (∀ who, M.BehavioralPolicy who) → Index → ℝ
  timingFactor : (∀ who, M.BehavioralPolicy who) → Index → Label → ℝ
  reach_factored : ∀ profile index label,
    finiteHistoryReach profile who (site index) (histories index label) =
      prefixLikelihood profile label * observationFactor profile index *
        timingFactor profile index label
  timing_tendsto : ∀ (sequence : ℕ → M.BehavioralAssessment) (A : M.BehavioralAssessment),
    BehavioralAssessmentConvergesPointwise sequence A → ∀ index label,
      Tendsto (fun n => timingFactor (sequence n).strategy index label) atTop
        (nhds (timingFactor A.strategy index label))

end GameTheory.Protocol.InformationModel
