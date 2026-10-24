/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

private theorem alarm_charge_integrable (law : PMF Outcome)
    (observe : Outcome → Observation) (alarm : Observation → PMF Bool) (penalty : ℝ) :
    PayoffIntegrable law (fun outcome => ((alarm (observe outcome)) true).toReal * penalty) :=
  payoffIntegrable_of_bounded _ _ (C := |penalty|) fun outcome => by
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_left (abs_nonneg _) (pmf_toReal_apply_le_one _ _)

/-- A finite automatically collected sanction preserves integrability of the
base utility, for arbitrary outcome and observation carriers. -/
theorem payoffIntegrable_monitoredUtility (law : PMF Outcome) (base : Outcome → ℝ)
    (observe : Outcome → Observation) (alarm : Observation → PMF Bool) (penalty : ℝ)
    (integrable : PayoffIntegrable law base) :
    PayoffIntegrable law (monitoredUtility base observe alarm penalty) := by
  rw [monitoredUtility_eq]
  exact payoffIntegrable_sub integrable (alarm_charge_integrable law observe alarm penalty)

theorem expect_monitoredUtility (law : PMF Outcome) (base : Outcome → ℝ)
    (observe : Outcome → Observation) (alarm : Observation → PMF Bool) (penalty : ℝ)
    (integrable : PayoffIntegrable law base) :
    expect law (monitoredUtility base observe alarm penalty) =
      expect law base - (((law.map observe).bind alarm) true).toReal * penalty := by
  rw [monitoredUtility_eq,
    expect_sub integrable (alarm_charge_integrable law observe alarm penalty)]
  simp_rw [mul_comm _ penalty]
  rw [expect_const_mul, toReal_bind_apply, expect_map]
  rfl

/-- The actual guarded incentive comparison after collection is the base
comparison adjusted by each law's own detection probability. -/
theorem holds_monitoredUtility_iff (prescribed deviating : PMF Outcome) (base : Outcome → ℝ)
    (observe : Outcome → Observation) (alarm : Observation → PMF Bool) (penalty : ℝ)
    (prescribedIntegrable : PayoffIntegrable prescribed base)
    (deviatingIntegrable : PayoffIntegrable deviating base) :
    (IncentiveComparison.mk prescribed deviating).Holds
        (monitoredUtility base observe alarm penalty) ↔
      expect deviating base - (((deviating.map observe).bind alarm) true).toReal * penalty ≤
        expect prescribed base - (((prescribed.map observe).bind alarm) true).toReal * penalty := by
  rw [IncentiveComparison.holds_iff_of_integrable
    (IncentiveComparison.mk prescribed deviating) (monitoredUtility base observe alarm penalty)
    (payoffIntegrable_monitoredUtility prescribed base observe alarm penalty prescribedIntegrable)
    (payoffIntegrable_monitoredUtility deviating base observe alarm penalty deviatingIntegrable)]
  change expect deviating _ ≤ expect prescribed _ ↔ _
  rw [expect_monitoredUtility deviating base observe alarm penalty deviatingIntegrable,
    expect_monitoredUtility prescribed base observe alarm penalty prescribedIntegrable]

/-- For one strictly profitable comparison, a sound alarm and nonnegative
finite sanction deter the deviation exactly when its observable law has
positive mass outside the admitted set. The prescribed observable support
must lie in that set. This does not give one uniform penalty for a family of
deviations. -/
theorem exists_sound_sanction_iff (prescribed deviating : PMF Outcome) (base : Outcome → ℝ)
    (observe : Outcome → Observation) (admitted : Set Observation)
    (prescribedAdmitted : ∀ outcome ∈ prescribed.support, observe outcome ∈ admitted)
    (prescribedIntegrable : PayoffIntegrable prescribed base)
    (deviatingIntegrable : PayoffIntegrable deviating base)
    (profitable : expect prescribed base < expect deviating base) :
    (∃ (alarm : Observation → PMF Bool) (penalty : ℝ), 0 ≤ penalty ∧
      (∀ observation ∈ admitted, ((alarm observation) true).toReal = 0) ∧
      (IncentiveComparison.mk prescribed deviating).Holds
        (monitoredUtility base observe alarm penalty)) ↔
      0 < ((deviating.map observe).toOuterMeasure admittedᶜ).toReal := by
  have prescribedSilent (alarm : Observation → PMF Bool)
      (sound : ∀ observation ∈ admitted, ((alarm observation) true).toReal = 0) :
      (((prescribed.map observe).bind alarm) true).toReal = 0 := by
    apply (alarm_zero_iff _ _).mpr
    intro observation supported
    obtain ⟨outcome, member, rfl⟩ := PMF.support_map observe prescribed ▸ supported
    exact sound _ (prescribedAdmitted outcome member)
  constructor
  · rintro ⟨alarm, penalty, _nonnegative, sound, respected⟩
    have comparison := (holds_monitoredUtility_iff prescribed deviating base observe alarm penalty
      prescribedIntegrable deviatingIntegrable).mp respected
    rw [prescribedSilent alarm sound, zero_mul, sub_zero] at comparison
    have detectionPositive : 0 < (((deviating.map observe).bind alarm) true).toReal := by
      by_contra notPositive
      have zero : (((deviating.map observe).bind alarm) true).toReal = 0 :=
        le_antisymm (not_lt.mp notPositive) ENNReal.toReal_nonneg
      rw [zero, zero_mul, sub_zero] at comparison
      exact (not_lt_of_ge comparison) profitable
    exact detectionPositive.trans_le (alarm_detection_le_outside_mass _ admitted alarm sound)
  · intro positive
    let detection := ((deviating.map observe).toOuterMeasure admittedᶜ).toReal
    let penalty := (expect deviating base - expect prescribed base) / detection
    have sound : ∀ observation ∈ admitted,
        ((outsideAlarm admitted observation) true).toReal = 0 := by
      intro observation member
      simp [member]
    refine ⟨outsideAlarm admitted, penalty, div_nonneg (sub_nonneg.mpr profitable.le) positive.le,
      sound, ?_⟩
    apply (holds_monitoredUtility_iff prescribed deviating base observe (outsideAlarm admitted)
      penalty prescribedIntegrable deviatingIntegrable).mpr
    rw [prescribedSilent _ sound, zero_mul, sub_zero, outsideAlarm_detection]
    change expect deviating base - detection *
      ((expect deviating base - expect prescribed base) / detection) ≤ expect prescribed base
    rw [mul_div_cancel₀ _ positive.ne']
    linarith

end GameTheory.Enforcement
