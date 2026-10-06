/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Expectation

/-! # Closeness in total variation

Two laws are within `error` in total variation when every event's
probabilities differ by at most `error`. Closeness survives pushforward, chains
additively, and is preserved by a common start law with close kernels. A
lottery that takes one branch with probability at least `1 - error` is within
`error` of that branch.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {α β ι : Type*}

/-- `first` and `second` give every event probabilities that differ by at most
`error`. -/
def WithinTV (error : ℝ) (first second : PMF α) : Prop :=
  ∀ event : Set α, |(first.toOuterMeasure event).toReal -
    (second.toOuterMeasure event).toReal| ≤ error

theorem WithinTV.refl (μ : PMF α) : WithinTV 0 μ μ := fun event => by
  rw [sub_self, abs_zero]

theorem WithinTV.symm {error : ℝ} {μ ν : PMF α} (close : WithinTV error μ ν) :
    WithinTV error ν μ := fun event => by
  rw [abs_sub_comm]
  exact close event

theorem WithinTV.trans {first second : ℝ} {μ ν ρ : PMF α} (left : WithinTV first μ ν)
    (right : WithinTV second ν ρ) : WithinTV (first + second) μ ρ := fun event =>
  (abs_sub_le _ _ _).trans (add_le_add (left event) (right event))

theorem WithinTV.mono {first second : ℝ} {μ ν : PMF α} (le : first ≤ second)
    (close : WithinTV first μ ν) : WithinTV second μ ν := fun event =>
  (close event).trans le

/-- The probability of a single outcome differs by at most the error. -/
theorem WithinTV.apply {error : ℝ} {μ ν : PMF α} (close : WithinTV error μ ν) (a : α) :
    |(μ a).toReal - (ν a).toReal| ≤ error := by
  simpa only [PMF.toOuterMeasure_apply_singleton] using close {a}

theorem WithinTV.eq_of_zero {μ ν : PMF α} (close : WithinTV 0 μ ν) : μ = ν := by
  ext a
  have equal := abs_nonpos_iff.mp (close.apply a)
  exact (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top a) (ν.apply_ne_top a)).mp
    (sub_eq_zero.mp equal)

theorem WithinTV.map {error : ℝ} {μ ν : PMF α} (close : WithinTV error μ ν) (g : α → β) :
    WithinTV error (μ.map g) (ν.map g) := fun event => by
  simpa only [PMF.toOuterMeasure_map_apply] using close (g ⁻¹' event)

private theorem eventMass_bounded (μ : PMF α) (event : Set α) :
    |(μ.toOuterMeasure event).toReal| ≤ 1 := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one μ event)

/-- A common start law with kernels close on its support. -/
theorem WithinTV.bind_right {error : ℝ} (μ : PMF α) {first second : α → PMF β}
    (close : ∀ a ∈ μ.support, WithinTV error (first a) (second a)) :
    WithinTV error (μ.bind first) (μ.bind second) := fun event => by
  rw [toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind,
    ← expect_sub (payoffIntegrable_toReal_toOuterMeasure μ first event)
      (payoffIntegrable_toReal_toOuterMeasure μ second event)]
  have integrable : PayoffIntegrable μ fun a =>
      ((first a).toOuterMeasure event).toReal - ((second a).toOuterMeasure event).toReal :=
    payoffIntegrable_of_bounded μ _ (C := 2) fun a =>
      (abs_sub _ _).trans (by
        linarith [eventMass_bounded (first a) event, eventMass_bounded (second a) event])
  have upper := expect_le_const μ _ integrable error fun a member =>
    (abs_le.mp (close a member event)).2
  have lower := expect_le_const μ _ (payoffIntegrable_neg integrable) error fun a member =>
    by linarith [(abs_le.mp (close a member event)).1]
  rw [show (fun a => -(((first a).toOuterMeasure event).toReal -
      ((second a).toOuterMeasure event).toReal)) =
    fun a => -1 * (((first a).toOuterMeasure event).toReal -
      ((second a).toOuterMeasure event).toReal) from funext fun _ => by ring,
    expect_const_mul] at lower
  exact abs_le.mpr ⟨by linarith, upper⟩

/-- The probability of an event is the expectation of its indicator. -/
private theorem toReal_toOuterMeasure_eq_expect (μ : PMF α) (event : Set α) [DecidablePred
    (· ∈ event)] : (μ.toOuterMeasure event).toReal =
      expect μ (fun a => if a ∈ event then 1 else 0) := by
  have law := toReal_toOuterMeasure_bind μ PMF.pure event
  rw [PMF.bind_pure] at law
  rw [law]
  apply expect_congr_on_support
  intro a _
  rw [PMF.toOuterMeasure_pure_apply]
  split <;> simp

/-- Laws within `error` in total variation have expectations within
`error * range` of a payoff whose values on both supports lie in an interval
of length `range`. -/
theorem WithinTV.expect_sub_le {error : ℝ} {μ ν : PMF α} (close : WithinTV error μ ν)
    (f : α → ℝ) (low range : ℝ)
    (bounded : ∀ a, a ∈ μ.support ∨ a ∈ ν.support → low ≤ f a ∧ f a ≤ low + range) :
    expect μ f - expect ν f ≤ error * range := by
  classical
  let event : Set α := {a | ν a < μ a}
  let gap : α → ℝ := fun a => f a - low - range * if a ∈ event then 1 else 0
  have size (a : α) (member : a ∈ μ.support ∨ a ∈ ν.support) :
      |f a| ≤ |low| + |range| := by
    obtain ⟨lower, upper⟩ := bounded a member
    exact abs_le.mpr ⟨by linarith [neg_abs_le low, abs_nonneg range],
      by linarith [le_abs_self low, le_abs_self range]⟩
  have integrable (law : PMF α) (inside : ∀ a ∈ law.support, a ∈ μ.support ∨ a ∈ ν.support) :
      PayoffIntegrable law f :=
    payoffIntegrable_of_bounded_on_support law f fun a member => size a (inside a member)
  have indicatorIntegrable (law : PMF α) :
      PayoffIntegrable law (fun a => if a ∈ event then (1 : ℝ) else 0) :=
    payoffIntegrable_of_bounded law _ (C := 1) fun a => by split <;> simp
  have gapIntegrable (law : PMF α) (inside : ∀ a ∈ law.support, a ∈ μ.support ∨ a ∈ ν.support) :
      PayoffIntegrable law gap :=
    payoffIntegrable_sub (payoffIntegrable_sub (integrable law inside)
      (payoffIntegrable_constant law low)) (payoffIntegrable_const_mul (indicatorIntegrable law))
  have μInside : ∀ a ∈ μ.support, a ∈ μ.support ∨ a ∈ ν.support := fun a member => Or.inl member
  have νInside : ∀ a ∈ ν.support, a ∈ μ.support ∨ a ∈ ν.support := fun a member => Or.inr member
  have expand (law : PMF α) (inside : ∀ a ∈ law.support, a ∈ μ.support ∨ a ∈ ν.support) :
      expect law gap = expect law f - low - range * (law.toOuterMeasure event).toReal := by
    rw [toReal_toOuterMeasure_eq_expect, ← expect_const_mul,
      expect_sub (payoffIntegrable_sub (integrable law inside)
        (payoffIntegrable_constant law low)) (payoffIntegrable_const_mul (indicatorIntegrable law)),
      expect_sub (integrable law inside) (payoffIntegrable_constant law low), expect_constant]
  have pointwise (a : α) : (μ a).toReal * gap a ≤ (ν a).toReal * gap a := by
    by_cases inEvent : a ∈ event
    · have larger : ν a < μ a := inEvent
      have member : a ∈ μ.support := (PMF.mem_support_iff μ a).mpr (ne_of_gt
        (lt_of_le_of_lt (show (0 : ENNReal) ≤ ν a from zero_le) larger))
      have nonpositive : gap a ≤ 0 := by
        have upper := (bounded a (Or.inl member)).2
        simp only [gap, inEvent, ↓reduceIte, mul_one]
        linarith
      have ordered : (ν a).toReal ≤ (μ a).toReal :=
        (ENNReal.toReal_le_toReal (ν.apply_ne_top a) (μ.apply_ne_top a)).mpr larger.le
      nlinarith
    · have smaller : μ a ≤ ν a := not_lt.mp inEvent
      have ordered : (μ a).toReal ≤ (ν a).toReal :=
        (ENNReal.toReal_le_toReal (μ.apply_ne_top a) (ν.apply_ne_top a)).mpr smaller
      by_cases member : a ∈ ν.support
      · have nonnegative : 0 ≤ gap a := by
          have lower := (bounded a (Or.inr member)).1
          simp only [gap, inEvent, ↓reduceIte, mul_zero, sub_zero]
          linarith
        nlinarith
      · have zero : ν a = 0 := (PMF.apply_eq_zero_iff ν a).mpr member
        have alsoZero : μ a = 0 :=
          le_antisymm (zero ▸ smaller) (show (0 : ENNReal) ≤ μ a from zero_le)
        simp only [zero, alsoZero, ENNReal.toReal_zero, zero_mul, le_refl]
  have compared : expect μ gap ≤ expect ν gap :=
    Summable.tsum_le_tsum pointwise (gapIntegrable μ μInside).summable
      (gapIntegrable ν νInside).summable
  rw [expand μ μInside, expand ν νInside] at compared
  have massGap := (abs_le.mp (close event)).2
  rcases le_or_gt 0 range with nonnegative | negative
  · have scaled := mul_le_mul_of_nonneg_left massGap nonnegative
    linarith
  · obtain ⟨a, member⟩ := μ.support_nonempty
    have inside := bounded a (Or.inl member)
    linarith [inside.1, inside.2]

/-- A lottery that takes the branch at `index` with probability at least
`1 - error` is within `error` of that branch. -/
theorem WithinTV.of_bind_point (timing : PMF ι) (index : ι)
    (branch : ι → PMF α) {error : ℝ} (mass : 1 - (timing index).toReal ≤ error) :
    WithinTV error (timing.bind branch) (branch index) := fun event => by
  classical
  let gap := fun other : ι =>
    ((branch other).toOuterMeasure event).toReal - ((branch index).toOuterMeasure event).toReal
  let away := fun other : ι => (1 : ℝ) - if index = other then 1 else 0
  have bounded (other : ι) : |gap other| ≤ away other := by
    by_cases same : index = other
    · subst other
      simp [gap, away]
    · have first := eventMass_bounded (branch other) event
      have second := eventMass_bounded (branch index) event
      rw [abs_of_nonneg ENNReal.toReal_nonneg] at first second
      simp only [away, same, ↓reduceIte, sub_zero, gap]
      exact abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := (branch other).toOuterMeasure
        event)], by linarith [ENNReal.toReal_nonneg (a := (branch index).toOuterMeasure event)]⟩
  have gapIntegrable : PayoffIntegrable timing gap :=
    payoffIntegrable_of_bounded timing _ (C := 2) fun other =>
      (abs_sub _ _).trans (by
        linarith [eventMass_bounded (branch other) event, eventMass_bounded (branch index) event])
  have awayIntegrable : PayoffIntegrable timing away :=
    payoffIntegrable_of_bounded timing _ (C := 1) fun other => by
      by_cases same : index = other <;> simp [away, same]
  have awayValue : expect timing away = 1 - (timing index).toReal := by
    rw [show away = fun other => (1 : ℝ) - if index = other then 1 else 0 from rfl,
      expect_sub (payoffIntegrable_constant timing 1)
        (payoffIntegrable_of_bounded timing _ (C := 1) fun other => by
          by_cases same : index = other <;> simp [same]),
      expect_constant, expect_ite_eq, mul_one]
  have difference : ((timing.bind branch).toOuterMeasure event).toReal -
      ((branch index).toOuterMeasure event).toReal = expect timing gap := by
    rw [toReal_toOuterMeasure_bind, ← expect_constant timing
      ((branch index).toOuterMeasure event).toReal,
      ← expect_sub (payoffIntegrable_toReal_toOuterMeasure timing branch event)
        (payoffIntegrable_constant timing _)]
  rw [difference]
  have upper := expect_mono (fun other _ => (abs_le.mp (bounded other)).2) gapIntegrable
    awayIntegrable
  have lower := expect_mono (fun other _ => by linarith [(abs_le.mp (bounded other)).1])
    (payoffIntegrable_neg awayIntegrable) gapIntegrable
  rw [show (fun other => -away other) = fun other => -1 * away other from
    funext fun _ => by ring, expect_const_mul] at lower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PMF
