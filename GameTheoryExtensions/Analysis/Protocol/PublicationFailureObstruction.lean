/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Survival
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Publication failure under a bounded probabilistic service

At each opportunity an outage branch advances the physical state without
repairing a missing publication. The other branch is an arbitrary kernel: it
may include adaptive policies, fees, retries, and past observations. A positive
conditional outage floor therefore leaves a positive failure probability at
every finite horizon. The observable law cannot equal a source law that never
fails. These statements quantify over all policies, without equilibrium or
visibility assumptions, and concern a probabilistic service rather than a
contract that guarantees protected delivery.
-/

noncomputable section

namespace GameTheory.Protocol.PublicationFailure

open Math.Probability

variable {State Outcome : Type*}

private theorem event_mass_mix (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bounded : weight ≤ 1) (first second : PMF State) (event : Set State) :
    ((mix weight nonnegative bounded first second).toOuterMeasure event).toReal =
      weight * (first.toOuterMeasure event).toReal +
        (1 - weight) * (second.toOuterMeasure event).toReal := by
  classical
  rw [← expect_indicator,
    expect_mix weight nonnegative bounded first second _
      (payoffIntegrable_ite_one_zero first (· ∈ event))
      (payoffIntegrable_ite_one_zero second (· ∈ event)),
    expect_indicator, expect_indicator]

/-- A physical opportunity has an outage branch and an unrestricted service
branch. The outage transition may advance clocks and record the opportunity. -/
def outageKernel (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (outage : State → State) (service : State → PMF State) (state : State) : PMF State :=
  mix floor nonnegative bounded (PMF.pure (outage state)) (service state)

/-- The explicit outage branch supplies the conditional failure floor. -/
theorem outageKernel_failure_floor (floor : ℝ) (nonnegative : 0 ≤ floor)
    (bounded : floor ≤ 1) (outage : State → State) (service : State → PMF State)
    (failed : Set State) (preserves : ∀ state ∈ failed, outage state ∈ failed)
    (state : State) (member : state ∈ failed) :
    floor ≤ ((outageKernel floor nonnegative bounded outage service state).toOuterMeasure
      failed).toReal := by
  classical
  unfold outageKernel
  rw [event_mass_mix, PMF.toOuterMeasure_pure_apply]
  simp only [preserves state member, ite_true, ENNReal.toReal_one, mul_one]
  have additional := mul_nonneg (show 0 ≤ 1 - floor by linarith)
    (show 0 ≤ ((service state).toOuterMeasure failed).toReal from ENNReal.toReal_nonneg)
  linarith

/-- No choice of the unrestricted service kernel removes the finite-horizon
failure mass supplied by the outage branch. States may encode the whole past. -/
theorem outageRun_failure_probability (initial : PMF State) (floor : ℝ)
    (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (outage : State → State) (service : State → PMF State) (failed : Set State)
    (preserves : ∀ state ∈ failed, outage state ∈ failed) (count : Nat) :
    floor ^ count * (initial.toOuterMeasure failed).toReal ≤
      (((fun law : PMF State =>
          law.bind (outageKernel floor nonnegative bounded outage service))^[count]
        initial).toOuterMeasure failed).toReal :=
  eventProbability_iterate_ge_pow initial _ failed floor nonnegative
    (outageKernel_failure_floor floor nonnegative bounded outage service failed preserves)
    count

/-- Observable failure mass lower-bounds every total-variation error against
a source law without that failure event. -/
theorem outageRun_totalVariation_lower_bound (initial : PMF State) (floor : ℝ)
    (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (outage : State → State) (service : State → PMF State)
    (observe : State → Outcome) (failed : Set Outcome)
    (preserves : ∀ state, observe state ∈ failed → observe (outage state) ∈ failed)
    (source : PMF Outcome) (sourceNeverFails : (source.toOuterMeasure failed).toReal = 0)
    (count : Nat) {error : ℝ}
    (close : PMF.WithinTV error
      ((((fun law : PMF State =>
        law.bind (outageKernel floor nonnegative bounded outage service))^[count]
        initial).map observe)) source) :
    floor ^ count * (initial.toOuterMeasure (observe ⁻¹' failed)).toReal ≤ error := by
  have lower := outageRun_failure_probability initial floor nonnegative bounded
    outage service (observe ⁻¹' failed) (fun state member => preserves state member) count
  have upper := close failed
  rw [PMF.toOuterMeasure_map_apply, sourceNeverFails, sub_zero,
    abs_of_nonneg ENNReal.toReal_nonneg] at upper
  exact lower.trans upper

/-- A positive outage floor makes exact observable-law preservation impossible
from an initial state with positive missing-publication probability. -/
theorem outageRun_not_realized (initial : PMF State) (floor : ℝ)
    (positive : 0 < floor) (bounded : floor ≤ 1)
    (outage : State → State) (service : State → PMF State)
    (observe : State → Outcome) (failed : Set Outcome)
    (preserves : ∀ state, observe state ∈ failed → observe (outage state) ∈ failed)
    (initialMissing : 0 < (initial.toOuterMeasure (observe ⁻¹' failed)).toReal)
    (source : PMF Outcome) (sourceNeverFails : (source.toOuterMeasure failed).toReal = 0)
    (count : Nat) :
    (((fun law : PMF State =>
      law.bind (outageKernel floor positive.le bounded outage service))^[count]
      initial).map observe) ≠ source := by
  intro same
  have close : PMF.WithinTV 0
      ((((fun law : PMF State =>
        law.bind (outageKernel floor positive.le bounded outage service))^[count]
        initial).map observe)) source := by
    rw [same]
    exact PMF.WithinTV.refl _
  have lower := outageRun_totalVariation_lower_bound initial floor positive.le bounded
    outage service observe failed preserves source sourceNeverFails count close
  exact (not_le_of_gt (mul_pos (pow_pos positive count) initialMissing)) lower

/-- An explicit binary publication model: initially unpublished, the outage
branch leaves the bit unchanged. Every choice of the other service kernel
has error at least `floor ^ count`. -/
theorem binary_publication_error (floor : ℝ) (nonnegative : 0 ≤ floor)
    (bounded : floor ≤ 1) (service : Bool → PMF Bool) (count : Nat) {error : ℝ}
    (close : PMF.WithinTV error
      (((fun law : PMF Bool =>
        law.bind (outageKernel floor nonnegative bounded id service))^[count]
        (PMF.pure false))) (PMF.pure true)) :
    floor ^ count ≤ error := by
  have bound := outageRun_totalVariation_lower_bound (PMF.pure false) floor
    nonnegative bounded id service id {false} (fun _ member => member)
    (PMF.pure true) (by simp) count (by simpa only [PMF.map_id] using close)
  simpa using bound

/-- A single unrecovered outage lottery is enough for nonrealization, even
when the normal branch offers deterministic protected inclusion. -/
theorem global_outage_totalVariation_lower_bound (floor : ℝ)
    (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (outage normal source : PMF Outcome) (failed : Set Outcome)
    (outageFails : (outage.toOuterMeasure failed).toReal = 1)
    (sourceNeverFails : (source.toOuterMeasure failed).toReal = 0) {error : ℝ}
    (close : PMF.WithinTV error (mix floor nonnegative bounded outage normal) source) :
    floor ≤ error := by
  have upper := close failed
  rw [sourceNeverFails, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg,
    event_mass_mix, outageFails, mul_one] at upper
  have additional := mul_nonneg (show 0 ≤ 1 - floor by linarith)
    (show 0 ≤ (normal.toOuterMeasure failed).toReal from ENNReal.toReal_nonneg)
  linarith

end GameTheory.Protocol.PublicationFailure
