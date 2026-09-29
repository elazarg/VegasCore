/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Enforcement
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

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

/-- Soundness for all permitted laws is exactly pointwise silence on the
union of their supports. This includes all permitted choices, not just the
chosen equilibrium's observations. -/
theorem sound_for_family_iff (permitted : Index → PMF Observation)
    (alarm : Observation → PMF Bool) :
    (∀ index, (((permitted index).bind alarm) true).toReal = 0) ↔
      ∀ observation ∈ ⋃ index, (permitted index).support,
        ((alarm observation) true).toReal = 0 := by
  simp only [alarm_zero_iff, Set.mem_iUnion, forall_exists_index]
  constructor <;> intro sound first second supported <;> exact sound second first supported

/-- Detection cannot exceed the deviating mass outside the admitted set. -/
theorem detection_le_outside_admitted (admitted : Set Observation)
    (law : PMF Observation) (alarm : Observation → PMF Bool)
    (sound : ∀ observation ∈ admitted, ((alarm observation) true).toReal = 0) :
    ((law.bind alarm) true).toReal ≤ (law.toOuterMeasure admittedᶜ).toReal := by
  classical
  rw [toReal_bind_apply, ← expect_indicator]
  apply FinDist.expect_mono
  intro observation _
  by_cases allowed : observation ∈ admitted
  · rw [sound observation allowed]
    simp [allowed]
  · simp only [Set.mem_compl_iff, allowed, not_false_eq_true, ite_true]
    exact pmf_toReal_apply_le_one (alarm observation) true

def outsideAlarm (admitted : Set Observation) (observation : Observation) : PMF Bool := by
  classical
  exact PMF.pure (decide (observation ∉ admitted))

theorem outsideAlarm_sound (admitted : Set Observation) :
    ∀ observation ∈ admitted, ((outsideAlarm admitted observation) true).toReal = 0 := by
  intro observation allowed
  simp [outsideAlarm, allowed, toReal_pure_apply]

theorem outsideAlarm_probability (admitted : Set Observation) (law : PMF Observation) :
    ((law.bind (outsideAlarm admitted)) true).toReal = (law.toOuterMeasure admittedᶜ).toReal := by
  classical
  rw [toReal_bind_apply, ← expect_indicator]
  apply expect_congr_on_support
  intro observation _
  by_cases allowed : observation ∈ admitted <;>
    simp [outsideAlarm, allowed, toReal_pure_apply]

/-- Expected utility after a terminal randomized alarm and automatic collection.
The monitor only sees the projection `observe` of the underlying outcome. -/
def monitoredUtility (base : Outcome → ℝ) (observe : Outcome → Observation)
    (alarm : Observation → PMF Bool) (penalty : ℝ) (outcome : Outcome) : ℝ :=
  expect ((alarm (observe outcome)).map (fun charged =>
    base outcome - if charged then penalty else 0)) id

theorem expect_monitoredUtility (law : PMF Outcome) (base : Outcome → ℝ)
    (observe : Outcome → Observation) (alarm : Observation → PMF Bool) (penalty : ℝ) :
    expect law (monitoredUtility base observe alarm penalty) =
      expect law base - (((law.map observe).bind alarm) true).toReal * penalty := by
  have pointwise (outcome : Outcome) : monitoredUtility base observe alarm penalty outcome =
      base outcome - ((alarm (observe outcome)) true).toReal * penalty := by
    unfold monitoredUtility
    rw [expect_map]
    simp only [id_eq]
    rw [FinDist.expect_sub, expect_constant]
    have same : (fun charged : Bool => if charged then penalty else 0) =
        (fun charged : Bool => (if charged = true then (1 : ℝ) else 0) * penalty) := by
      funext charged
      cases charged <;> simp
    rw [same, FinDist.expect_mul_const]
    change base outcome - (expect (alarm (observe outcome))
      (fun charged => if charged ∈ ({true} : Set Bool) then 1 else 0)) * penalty = _
    rw [expect_indicator, FinDist.probOf_singleton]
  rw [show monitoredUtility base observe alarm penalty =
    (fun outcome => base outcome - ((alarm (observe outcome)) true).toReal * penalty) from
      funext pointwise]
  rw [FinDist.expect_sub, FinDist.expect_mul_const, toReal_bind_apply, expect_map]

/-- The optimal sound alarm deters a comparison at a specified nonnegative
penalty exactly when the detectable mass times that penalty covers the gain. -/
theorem exists_sound_alarm_for_penalty_iff (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (observe : Outcome → Observation) (admitted : Set Observation)
    (permitted : (comparison.prescribed.map observe).support ⊆ admitted)
    (penalty : ℝ) (nonnegative : 0 ≤ penalty) :
    (∃ alarm : Observation → PMF Bool,
      (∀ observation ∈ admitted, ((alarm observation) true).toReal = 0) ∧
      comparison.Holds (monitoredUtility base observe alarm penalty)) ↔
        expect comparison.alternative base - expect comparison.prescribed base ≤
          ((comparison.alternative.map observe).toOuterMeasure admittedᶜ).toReal * penalty := by
  constructor
  · rintro ⟨alarm, sound, deters⟩
    have silent : (((comparison.prescribed.map observe).bind alarm) true).toReal = 0 :=
      (alarm_zero_iff _ alarm).mpr (fun observation supported =>
        sound observation (permitted supported))
    have bounded := mul_le_mul_of_nonneg_right
      (detection_le_outside_admitted admitted (comparison.alternative.map observe) alarm sound)
      nonnegative
    change expect comparison.alternative _ ≤ expect comparison.prescribed _ at deters
    rw [expect_monitoredUtility, expect_monitoredUtility, silent, zero_mul, sub_zero] at deters
    linarith
  · intro sufficient
    have silent :
        (((comparison.prescribed.map observe).bind (outsideAlarm admitted)) true).toReal = 0 :=
      (alarm_zero_iff _ _).mpr (fun observation supported =>
        outsideAlarm_sound admitted observation (permitted supported))
    refine ⟨outsideAlarm admitted, outsideAlarm_sound admitted, ?_⟩
    change expect comparison.alternative _ ≤ expect comparison.prescribed _
    rw [expect_monitoredUtility, expect_monitoredUtility, silent, zero_mul, sub_zero,
      outsideAlarm_probability]
    linarith

/-- For one profitable comparison, a finite nonnegative penalty and a sound
alarm can deter the deviation iff it has positive observable mass outside
the admitted set. This does not give a uniform penalty for a family of deviations. -/
theorem exists_sound_deterrent_iff (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (observe : Outcome → Observation) (admitted : Set Observation)
    (permitted : (comparison.prescribed.map observe).support ⊆ admitted)
    (profitable : expect comparison.prescribed base < expect comparison.alternative base) :
    (∃ alarm : Observation → PMF Bool, ∃ penalty : ℝ,
      0 ≤ penalty ∧
      (∀ observation ∈ admitted, ((alarm observation) true).toReal = 0) ∧
      comparison.Holds (monitoredUtility base observe alarm penalty)) ↔
        0 < ((comparison.alternative.map observe).toOuterMeasure admittedᶜ).toReal := by
  constructor
  · rintro ⟨alarm, penalty, nonnegative, sound, deters⟩
    have silent : (((comparison.prescribed.map observe).bind alarm) true).toReal = 0 :=
      (alarm_zero_iff _ alarm).mpr (fun observation supported =>
        sound observation (permitted supported))
    have bounded := detection_le_outside_admitted admitted
      (comparison.alternative.map observe) alarm sound
    have detected_nonnegative :=
      ENNReal.toReal_nonneg
    change expect comparison.alternative _ ≤ expect comparison.prescribed _ at deters
    rw [expect_monitoredUtility, expect_monitoredUtility, silent, zero_mul, sub_zero] at deters
    have detected : 0 < (((comparison.alternative.map observe).bind alarm) true).toReal := by
      by_contra impossible
      have zero : (((comparison.alternative.map observe).bind alarm) true).toReal = 0 :=
        le_antisymm (le_of_not_gt impossible) detected_nonnegative
      rw [zero, zero_mul, sub_zero] at deters
      exact (not_le_of_gt profitable) deters
    exact detected.trans_le bounded
  · intro positive
    let gain := expect comparison.alternative base - expect comparison.prescribed base
    let probability := ((comparison.alternative.map observe).toOuterMeasure admittedᶜ).toReal
    have probability_positive : 0 < probability := positive
    have gain_positive : 0 < gain := sub_pos.mpr profitable
    have silent :
        (((comparison.prescribed.map observe).bind (outsideAlarm admitted)) true).toReal = 0 :=
      (alarm_zero_iff _ _).mpr (fun observation supported =>
        outsideAlarm_sound admitted observation (permitted supported))
    refine ⟨outsideAlarm admitted, gain / probability,
      (div_pos gain_positive probability_positive).le,
      outsideAlarm_sound admitted, ?_⟩
    change expect comparison.alternative _ ≤ expect comparison.prescribed _
    rw [expect_monitoredUtility, expect_monitoredUtility, silent, zero_mul, sub_zero,
      outsideAlarm_probability]
    change expect comparison.alternative base - probability * (gain / probability) ≤ _
    rw [mul_div_cancel₀ _ probability_positive.ne']
    dsimp only [gain]
    linarith

end GameTheory.Enforcement
