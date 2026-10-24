/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.DiscretePushforward
import GameTheory.Math.Probability.Uniform

/-! # Discrete readouts on an uncountable ambient carrier

An actual measurable readout divides a two-atom real-valued draw by two. Every
function of the readout is AE measurable, regardless of its values off the two
real atoms. The integral depends only on the two supported values.
-/

noncomputable section

namespace GameTheoryExtensionsTests.DiscretePushforward

open GameTheory.Math.Probability MeasureTheory

private def coin : PMF Bool := PMF.uniformOfFintype Bool

private def sourceLaw : PMF ℝ := coin.map fun bit => if bit then 2 else 0

private def points (bit : Bool) : ℝ := if bit then 1 else 0

private def targetLaw : PMF ℝ := coin.map points

private def sourceMeasure : Measure ℝ := sourceLaw.toMeasure

private def readout (value : ℝ) : ℝ := value / 2

theorem readout_measurable : Measurable readout := measurable_id.div_const 2

theorem readout_law : sourceMeasure.map readout = targetLaw.toMeasure := by
  rw [sourceMeasure, PMF.toMeasure_map readout sourceLaw readout_measurable]
  congr 1
  rw [sourceLaw, targetLaw, PMF.map_comp]
  congr 1
  funext bit
  cases bit <;> norm_num [Function.comp_def, points, readout]

theorem target_support_finite : targetLaw.support.Finite := by
  rw [targetLaw, PMF.support_map]
  exact (Set.toFinite coin.support).image points

/-- No measurability or countability premise is imposed on this arbitrary
real-indexed value function. The actual projection is proved measurable above. -/
theorem arbitrary_value_aemeasurable (value : ℝ → ℝ) :
    AEMeasurable (value ∘ readout) sourceMeasure :=
  aemeasurable_of_pmf_pushforward sourceMeasure targetLaw readout
    readout_measurable readout_law value

/-- Assigning zero and two at the supported readout atoms gives integral one,
whatever values the function takes elsewhere in the real numbers. -/
theorem integral_from_supported_values (value : ℝ → ENNReal)
    (atZero : value 0 = 0) (atOne : value 1 = 2) :
    (∫⁻ source, value (readout source) ∂sourceMeasure) = 1 := by
  rw [lintegral_of_pmf_pushforward sourceMeasure targetLaw readout
    readout_measurable readout_law value]
  have atoms := lintegral_of_pmf_pushforward coin.toMeasure targetLaw points
    (measurable_of_countable points)
    (PMF.toMeasure_map points coin (measurable_of_countable points))
    value
  rw [← atoms, lintegral_fintype]
  norm_num [Fintype.sum_bool, points, atZero, atOne, coin,
    PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

end GameTheoryExtensionsTests.DiscretePushforward
