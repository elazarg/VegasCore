/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Enforcement

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
theorem sound_for_family_iff (permitted : Index → FinDist Observation)
    (alarm : Observation → FinDist Bool) :
    (∀ index, ((permitted index).bind alarm).prob true = 0) ↔
      ∀ observation ∈ ⋃ index, (permitted index).support,
        (alarm observation).prob true = 0 := by
  simp only [alarm_zero_iff, Set.mem_iUnion, forall_exists_index]
  constructor <;> intro sound first second supported <;> exact sound second first supported

/-- Detection cannot exceed the deviating mass outside the admitted set. -/
theorem detection_le_outside_admitted (admitted : Set Observation)
    (law : FinDist Observation) (alarm : Observation → FinDist Bool)
    (sound : ∀ observation ∈ admitted, (alarm observation).prob true = 0) :
    (law.bind alarm).prob true ≤ law.probOf admittedᶜ := by
  classical
  rw [FinDist.prob_bind, ← FinDist.expect_indicator_eq_probOf]
  apply FinDist.expect_mono
  intro observation _
  by_cases allowed : observation ∈ admitted
  · rw [sound observation allowed]
    simp [allowed]
  · simp only [Set.mem_compl_iff, allowed, not_false_eq_true, ite_true]
    exact (alarm observation).prob_le_one true

def outsideAlarm (admitted : Set Observation) (observation : Observation) : FinDist Bool := by
  classical
  exact FinDist.pure (decide (observation ∉ admitted))

theorem outsideAlarm_sound (admitted : Set Observation) :
    ∀ observation ∈ admitted, (outsideAlarm admitted observation).prob true = 0 := by
  intro observation allowed
  simp [outsideAlarm, allowed, FinDist.prob_pure_eq_ite]

theorem outsideAlarm_probability (admitted : Set Observation) (law : FinDist Observation) :
    (law.bind (outsideAlarm admitted)).prob true = law.probOf admittedᶜ := by
  classical
  rw [FinDist.prob_bind, ← FinDist.expect_indicator_eq_probOf]
  apply FinDist.expect_congr
  intro observation _
  by_cases allowed : observation ∈ admitted <;>
    simp [outsideAlarm, allowed, FinDist.prob_pure_eq_ite]

/-- Expected utility after a terminal randomized alarm and automatic collection.
The monitor only sees the projection `observe` of the underlying outcome. -/
def monitoredUtility (base : Outcome → ℝ) (observe : Outcome → Observation)
    (alarm : Observation → FinDist Bool) (penalty : ℝ) (outcome : Outcome) : ℝ :=
  ((alarm (observe outcome)).map (fun charged =>
    base outcome - if charged then penalty else 0)).expect id

theorem expect_monitoredUtility (law : FinDist Outcome) (base : Outcome → ℝ)
    (observe : Outcome → Observation) (alarm : Observation → FinDist Bool) (penalty : ℝ) :
    law.expect (monitoredUtility base observe alarm penalty) =
      law.expect base - ((law.map observe).bind alarm).prob true * penalty := by
  have pointwise (outcome : Outcome) : monitoredUtility base observe alarm penalty outcome =
      base outcome - (alarm (observe outcome)).prob true * penalty := by
    unfold monitoredUtility
    rw [FinDist.expect_map]
    simp only [id_eq]
    rw [FinDist.expect_sub, FinDist.expect_const]
    have same : (fun charged : Bool => if charged then penalty else 0) =
        (fun charged : Bool => (if charged = true then (1 : ℝ) else 0) * penalty) := by
      funext charged
      cases charged <;> simp
    rw [same, FinDist.expect_mul_const]
    change base outcome - ((alarm (observe outcome)).expect
      (fun charged => if charged ∈ ({true} : Set Bool) then 1 else 0)) * penalty = _
    rw [FinDist.expect_indicator_eq_probOf, FinDist.probOf_singleton]
  rw [show monitoredUtility base observe alarm penalty =
    (fun outcome => base outcome - (alarm (observe outcome)).prob true * penalty) from
      funext pointwise]
  rw [FinDist.expect_sub, FinDist.expect_mul_const, FinDist.prob_bind, FinDist.expect_map]

/-- The optimal sound alarm deters a comparison at a specified nonnegative
penalty exactly when the detectable mass times that penalty covers the gain. -/
theorem exists_sound_alarm_for_penalty_iff (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (observe : Outcome → Observation) (admitted : Set Observation)
    (permitted : (comparison.prescribed.map observe).support ⊆ admitted)
    (penalty : ℝ) (nonnegative : 0 ≤ penalty) :
    (∃ alarm : Observation → FinDist Bool,
      (∀ observation ∈ admitted, (alarm observation).prob true = 0) ∧
      comparison.Holds (monitoredUtility base observe alarm penalty)) ↔
        comparison.alternative.expect base - comparison.prescribed.expect base ≤
          (comparison.alternative.map observe).probOf admittedᶜ * penalty := by
  constructor
  · rintro ⟨alarm, sound, deters⟩
    have silent : ((comparison.prescribed.map observe).bind alarm).prob true = 0 :=
      (alarm_zero_iff _ alarm).mpr (fun observation supported =>
        sound observation (permitted supported))
    have bounded := mul_le_mul_of_nonneg_right
      (detection_le_outside_admitted admitted (comparison.alternative.map observe) alarm sound)
      nonnegative
    change comparison.alternative.expect _ ≤ comparison.prescribed.expect _ at deters
    rw [expect_monitoredUtility, expect_monitoredUtility, silent, zero_mul, sub_zero] at deters
    linarith
  · intro sufficient
    have silent :
        ((comparison.prescribed.map observe).bind (outsideAlarm admitted)).prob true = 0 :=
      (alarm_zero_iff _ _).mpr (fun observation supported =>
        outsideAlarm_sound admitted observation (permitted supported))
    refine ⟨outsideAlarm admitted, outsideAlarm_sound admitted, ?_⟩
    change comparison.alternative.expect _ ≤ comparison.prescribed.expect _
    rw [expect_monitoredUtility, expect_monitoredUtility, silent, zero_mul, sub_zero,
      outsideAlarm_probability]
    linarith

/-- For one profitable comparison, a finite nonnegative penalty and a sound
alarm can deter the deviation iff it has positive observable mass outside
the admitted set. This does not give a uniform penalty for a family of deviations. -/
theorem exists_sound_deterrent_iff (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (observe : Outcome → Observation) (admitted : Set Observation)
    (permitted : (comparison.prescribed.map observe).support ⊆ admitted)
    (profitable : comparison.prescribed.expect base < comparison.alternative.expect base) :
    (∃ alarm : Observation → FinDist Bool, ∃ penalty : ℝ,
      0 ≤ penalty ∧
      (∀ observation ∈ admitted, (alarm observation).prob true = 0) ∧
      comparison.Holds (monitoredUtility base observe alarm penalty)) ↔
        0 < (comparison.alternative.map observe).probOf admittedᶜ := by
  constructor
  · rintro ⟨alarm, penalty, nonnegative, sound, deters⟩
    have silent : ((comparison.prescribed.map observe).bind alarm).prob true = 0 :=
      (alarm_zero_iff _ alarm).mpr (fun observation supported =>
        sound observation (permitted supported))
    have bounded := detection_le_outside_admitted admitted
      (comparison.alternative.map observe) alarm sound
    have detected_nonnegative :=
      ((comparison.alternative.map observe).bind alarm).prob_nonneg true
    change comparison.alternative.expect _ ≤ comparison.prescribed.expect _ at deters
    rw [expect_monitoredUtility, expect_monitoredUtility, silent, zero_mul, sub_zero] at deters
    have detected : 0 < ((comparison.alternative.map observe).bind alarm).prob true := by
      by_contra impossible
      have zero : ((comparison.alternative.map observe).bind alarm).prob true = 0 :=
        le_antisymm (le_of_not_gt impossible) detected_nonnegative
      rw [zero, zero_mul, sub_zero] at deters
      exact (not_le_of_gt profitable) deters
    exact detected.trans_le bounded
  · intro positive
    let gain := comparison.alternative.expect base - comparison.prescribed.expect base
    let probability := (comparison.alternative.map observe).probOf admittedᶜ
    have probability_positive : 0 < probability := positive
    have gain_positive : 0 < gain := sub_pos.mpr profitable
    have silent :
        ((comparison.prescribed.map observe).bind (outsideAlarm admitted)).prob true = 0 :=
      (alarm_zero_iff _ _).mpr (fun observation supported =>
        outsideAlarm_sound admitted observation (permitted supported))
    refine ⟨outsideAlarm admitted, gain / probability,
      (div_pos gain_positive probability_positive).le,
      outsideAlarm_sound admitted, ?_⟩
    change comparison.alternative.expect _ ≤ comparison.prescribed.expect _
    rw [expect_monitoredUtility, expect_monitoredUtility, silent, zero_mul, sub_zero,
      outsideAlarm_probability]
    change comparison.alternative.expect base - probability * (gain / probability) ≤ _
    rw [mul_div_cancel₀ _ probability_positive.ne']
    dsimp only [gain]
    linarith

end GameTheory.Enforcement
