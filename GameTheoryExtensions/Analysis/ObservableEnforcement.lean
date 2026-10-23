/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Enforcement
import GameTheory.Analysis.IncentiveCone

/-! # When observable violations admit a sound deterrent

The admitted observations may contain the supports of every permitted source
strategy. A randomized alarm must be silent on all of them. For a particular
profitable deviation, a finite sound sanction exists exactly when its
observation law assigns positive mass outside that set.

This is a conditional incentive comparison, not a sequential-equilibrium or
report-delivery theorem. The charge is collected whenever the alarm fires.
Its amount is utility, and may depend on the compared laws and base utility.
-/

noncomputable section

namespace GameTheory.Enforcement

open Math.Probability

variable {Outcome Observation Index : Type*}

/-- Expected utility after a terminal randomized alarm and automatic collection.
The monitor only sees the projection `observe` of the underlying outcome. -/
def monitoredUtility (base : Outcome → ℝ) (observe : Outcome → Observation)
    (alarm : Observation → PMF Bool) (penalty : ℝ) (outcome : Outcome) : ℝ :=
  expect ((alarm (observe outcome)).map (fun charged =>
    base outcome - if charged then penalty else 0)) id

/-- Collection subtracts the penalty times the probability that the alarm
fires at the observed outcome. -/
theorem monitoredUtility_eq (base : Outcome → ℝ) (observe : Outcome → Observation)
    (alarm : Observation → PMF Bool) (penalty : ℝ) :
    monitoredUtility base observe alarm penalty =
      fun outcome => base outcome - ((alarm (observe outcome)) true).toReal * penalty := by
  funext outcome
  unfold monitoredUtility
  rw [expect_map, expect_eq_sum]
  simp only [Fintype.sum_bool, Function.comp_apply, id_eq, ↓reduceIte, Bool.false_eq_true,
    sub_zero]
  have total := pmf_sum_toReal_eq_one (alarm (observe outcome))
  simp only [Fintype.sum_bool] at total
  linear_combination (base outcome) * total

theorem expect_monitoredUtility (law : PMF Outcome) (base : Outcome → ℝ)
    (observe : Outcome → Observation) (alarm : Observation → PMF Bool) (penalty : ℝ)
    (integrable : PayoffIntegrable law base) :
    expect law (monitoredUtility base observe alarm penalty) =
      expect law base - (((law.map observe).bind alarm) true).toReal * penalty := by
  rw [monitoredUtility_eq, expect_sub integrable
    (payoffIntegrable_of_bounded _ _ (C := |penalty|) fun outcome => by
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_of_le_one_left (abs_nonneg _) (pmf_toReal_apply_le_one _ _))]
  simp_rw [mul_comm _ penalty]
  rw [expect_const_mul, toReal_bind_apply, expect_map]
  rfl

end GameTheory.Enforcement
