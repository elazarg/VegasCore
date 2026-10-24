/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.Measure

/-! # Observables through a discrete measure projection

A measurable readout with a PMF pushforward makes every function of that readout
almost everywhere measurable. Only the law's supported atoms enter the proof;
the ambient readout carrier need not be countable.
-/

noncomputable section

namespace GameTheory.Math.Probability

open MeasureTheory

/-- A measurable projection with a PMF marginal admits arbitrary readout values. -/
theorem aemeasurable_of_pmf_pushforward
    {Source Target Value : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target] [MeasurableSingletonClass Target]
    [MeasurableSpace Value] [Nonempty Value]
    (measure : Measure Source) (law : PMF Target) (project : Source → Target)
    (measurable : Measurable project) (pushforward : measure.map project = law.toMeasure)
    (value : Target → Value) : AEMeasurable (value ∘ project) measure := by
  have full : law.toMeasure law.supportᶜ = 0 :=
    (law.toMeasure_apply_eq_zero_iff law.support_countable.measurableSet.compl).2
      (by
        apply Set.disjoint_left.mpr
        intro outcome supported outside
        exact outside supported)
  have mapped : AEMeasurable value (measure.map project) := by
    rw [pushforward]
    exact aemeasurable_of_countable_full_set law.toMeasure value law.support
      law.support_countable full
  exact mapped.comp_measurable measurable

/-- Integrating a discrete readout uses its PMF marginal, even when the value
function has no global measurability property on the ambient readout carrier. -/
theorem lintegral_of_pmf_pushforward
    {Source Target : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target] [MeasurableSingletonClass Target]
    (measure : Measure Source) (law : PMF Target) (project : Source → Target)
    (measurable : Measurable project) (pushforward : measure.map project = law.toMeasure)
    (value : Target → ENNReal) :
    (∫⁻ source, value (project source) ∂measure) = ∫⁻ target, value target ∂law.toMeasure := by
  have mapped : AEMeasurable value (measure.map project) := by
    rw [pushforward]
    exact aemeasurable_of_pmf_pushforward law.toMeasure law id measurable_id (by simp) value
  rw [← pushforward]
  exact (lintegral_map' mapped measurable.aemeasurable).symm

end GameTheory.Math.Probability
