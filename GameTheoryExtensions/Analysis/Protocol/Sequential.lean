/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Sequential
import GameTheoryExtensions.Math.Probability.Support

/-! # Finite-menu requirements of finitely supported fully mixed assessments

A fully mixed assessment gives every legal choice positive probability. When
its local laws are finitely supported, every legal decision menu is therefore
finite. Full support alone does not bound a menu: a geometric law is fully
mixed on the natural numbers.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type} {E : ExecutionProtocol ι} {M : InformationModel E}

/-- Finite-support fully mixed assessments require finite legal decision menus. -/
theorem BehavioralAssessment.IsFullyMixed.finite_choice
    {assessment : M.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    (who : ι) (site : M.InformationSite who)
    (finiteSupport : (assessment.strategy who site.1).support.Finite) :
    Finite (M.Choice who site.1) :=
  FullSupport.finite finiteSupport (mixed who site)

/-- An infinite legal menu admits no finitely supported fully mixed law. -/
theorem BehavioralAssessment.not_isFullyMixed_of_infinite_choice
    (assessment : M.BehavioralAssessment) (who : ι) (site : M.InformationSite who)
    [Infinite (M.Choice who site.1)]
    (finiteSupport : (assessment.strategy who site.1).support.Finite) :
    ¬ assessment.IsFullyMixed := by
  intro mixed
  have := mixed.finite_choice who site finiteSupport
  exact not_finite (M.Choice who site.1)

end GameTheory.Protocol.InformationModel
