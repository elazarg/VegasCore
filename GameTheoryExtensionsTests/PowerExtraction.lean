/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.PowerCompleteness
import GameTheoryExtensionsTests.UnequalPowerEquilibrium

/-! # Extracting a certificate from an actual nonzero-payoff equilibrium

The input is the existing exact assessment's checked common-sequence
consistency. No action-rate, affine-ray or coefficient constraints are supplied
to the extraction theorem by this client.
-/

noncomputable section

namespace GameTheoryExtensionsTests.PowerExtraction

open GameTheory GameTheory.Protocol GameTheory.Protocol.InformationModel

open UnequalPowerEquilibrium

private local instance (who : Bool) : Finite (model.InfoState who) :=
  inferInstanceAs (Finite CyclicBeliefs.View)

private local instance : Finite UnequalPowerEquilibrium.arena.History :=
  (model.bayesAssessment_isFullyMixed UnequalPowerEquilibrium.uniformStrategy
    UnequalPowerEquilibrium.uniform_full UnequalPowerEquilibrium.antichain).finite_history
    UnequalPowerEquilibrium.bounded (fun _ _ => Set.toFinite _) (fun _ => Set.toFinite _)

/-- The exact unequal-order assessment admits shared positive coefficients
and integer powers as a consequence of actual game consistency. -/
theorem unequal_order_game_has_certificate :
    ∃ (coefficient : ∀ who info, model.Choice who info → ℝ)
      (order : ∀ who info, model.Choice who info → Nat)
      (reference : ∀ who (site : model.InformationSite who), model.InformationHistory who site.1),
      (∀ who info choice, 0 < coefficient who info choice) ∧
      (∀ who info choice,
        (if order who info choice = 0 then coefficient who info choice else 0) =
          (assessment.strategy who info choice).toReal) ∧
      (∀ who (site : model.InformationSite who) (history : model.InformationHistory who site.1),
        model.powerHistoryOrder order (reference who site).1.trace ≤
          model.powerHistoryOrder order history.1.trace) ∧
      (∀ who (site : model.InformationSite who) (history : model.InformationHistory who site.1),
        model.powerHistoryOrder order history.1.trace =
            model.powerHistoryOrder order (reference who site).1.trace ↔
          (assessment.belief who site history).toReal ≠ 0) ∧
      (∀ who (site : model.InformationSite who) (history : model.InformationHistory who site.1),
        (assessment.belief who site history).toReal ≠ 0 →
        model.powerHistoryCoefficient coefficient history.1.trace /
            model.powerHistoryCoefficient coefficient (reference who site).1.trace =
          (assessment.belief who site history).toReal /
            (assessment.belief who site (reference who site)).toReal) := by
  exact UnequalPowerEquilibrium.consistent.exists_power_certificate model

end GameTheoryExtensionsTests.PowerExtraction
