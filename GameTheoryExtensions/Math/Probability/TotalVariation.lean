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

/-- Any two laws are within one of each other. -/
theorem withinTV_one (μ ν : PMF α) : WithinTV 1 μ ν := fun event => by
  have first := eventMass_bounded μ event
  have second := eventMass_bounded ν event
  rw [abs_of_nonneg ENNReal.toReal_nonneg] at first second
  exact abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := μ.toOuterMeasure event)],
    by linarith [ENNReal.toReal_nonneg (a := ν.toOuterMeasure event)]⟩

/-- A common start law with kernels whose closeness varies with the start: the
laws are within the expected error. -/
theorem WithinTV.bind_right_expect (μ : PMF α) {first second : α → PMF β} (error : α → ℝ)
    (integrable : PayoffIntegrable μ error)
    (close : ∀ a ∈ μ.support, WithinTV (error a) (first a) (second a)) :
    WithinTV (expect μ error) (μ.bind first) (μ.bind second) := fun event => by
  rw [toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind,
    ← expect_sub (payoffIntegrable_toReal_toOuterMeasure μ first event)
      (payoffIntegrable_toReal_toOuterMeasure μ second event)]
  have differenceIntegrable : PayoffIntegrable μ fun a =>
      ((first a).toOuterMeasure event).toReal - ((second a).toOuterMeasure event).toReal :=
    payoffIntegrable_of_bounded μ _ (C := 2) fun a =>
      (abs_sub _ _).trans (by
        linarith [eventMass_bounded (first a) event, eventMass_bounded (second a) event])
  have upper := expect_mono (fun a member => (abs_le.mp (close a member event)).2)
    differenceIntegrable integrable
  have lower := expect_mono (fun a member => by linarith [(abs_le.mp (close a member event)).1])
    (payoffIntegrable_neg integrable) differenceIntegrable
  rw [expect_neg] at lower
  exact abs_le.mpr ⟨by linarith, upper⟩

/-- **Residual of a dominated law.** If a law on `Option γ` puts at most `ν c` on
each `some c`, then `ν` is that law with its `none` branch replaced by some
residual law on `γ`. -/
theorem exists_residual_of_le {γ : Type*} (π : PMF (Option γ)) (ν : PMF γ)
    (dominated : ∀ c, π (some c) ≤ ν c) :
    ∃ residual : PMF γ, π.bind (fun outcome => outcome.elim residual PMF.pure) = ν := by
  classical
  have optionSum (f : Option γ → ENNReal) : ∑' outcome, f outcome = f none + ∑' c, f (some c) := by
    rw [ENNReal.tsum_eq_add_tsum_ite none]
    congr 1
    symm
    convert Function.Injective.tsum_eq (Option.some_injective γ) (f := fun outcome =>
      if outcome = none then (0 : ENNReal) else f outcome) ?_ using 1
    · simp
    · exact tsum_congr fun outcome => by split_ifs <;> rfl
    · intro outcome member
      cases outcome with
      | none => simp at member
      | some c => exact ⟨c, rfl⟩
  have split : π none + ∑' c, π (some c) = 1 := by
    rw [← optionSum (fun outcome => π outcome)]
    exact π.tsum_coe
  have someFinite : ∑' c, π (some c) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (split ▸ le_add_self)
  have gap : ∑' c, (ν c - π (some c)) = π none := by
    have whole : ∑' c, (ν c - π (some c)) + ∑' c, π (some c) = 1 := by
      rw [← ENNReal.tsum_add]
      simp only [tsub_add_cancel_of_le (dominated _)]
      exact ν.tsum_coe
    rw [← ENNReal.add_sub_cancel_right someFinite (a := ∑' c, (ν c - π (some c))), whole,
      ← split, ENNReal.add_sub_cancel_right someFinite]
  have apply (residual : PMF γ) (c : γ) :
      (π.bind fun outcome => outcome.elim residual PMF.pure) c =
        π none * residual c + π (some c) := by
    rw [PMF.bind_apply, optionSum]
    congr 1
    rw [tsum_eq_single c fun other different => by
      simp [PMF.pure_apply, Ne.symm different]]
    simp [PMF.pure_apply]
  by_cases empty : π none = 0
  · refine ⟨ν, PMF.ext fun c => ?_⟩
    rw [apply, empty, zero_mul, zero_add]
    have zero : ν c - π (some c) = 0 :=
      ENNReal.tsum_eq_zero.mp (gap.trans empty) c
    exact le_antisymm (dominated c) (tsub_eq_zero_iff_le.mp zero)
  · have finite : π none ≠ ⊤ := PMF.apply_ne_top π none
    refine ⟨PMF.normalize (fun c => ν c - π (some c)) (gap ▸ empty) (gap ▸ finite),
      PMF.ext fun c => ?_⟩
    rw [apply, PMF.normalize_apply, gap, mul_comm, mul_assoc, ENNReal.inv_mul_cancel empty finite,
      mul_one, tsub_add_cancel_of_le (dominated c)]

/-- **Coupling up to failure.** A start law `μ` reads, through `decode`, either a
point of `γ` or a failure (`none`), and its successful readouts are dominated
by the law `ν`. If, after every successful start, the kernel `first` is within
`error` of `second` at the decoded point, then the two composed laws are within
the failure probability plus the expected error on success. -/
theorem WithinTV.bind_of_dominated {γ : Type*} (μ : PMF α) (ν : PMF γ)
    (decode : α → Option γ) (dominated : ∀ c, (μ.map decode) (some c) ≤ ν c)
    (first : α → PMF β) (second : γ → PMF β) (error : α → ℝ)
    (errorNonneg : ∀ a, 0 ≤ error a) (errorAtMostOne : ∀ a, error a ≤ 1)
    (close : ∀ a ∈ μ.support, ∀ c, decode a = some c → WithinTV (error a) (first a) (second c)) :
    WithinTV ((((μ.map decode) none).toReal) +
        expect μ fun a => if (decode a).isSome then error a else 0)
      (μ.bind first) (ν.bind second) := by
  classical
  obtain ⟨residual, rebuilt⟩ := exists_residual_of_le (μ.map decode) ν dominated
  let joined : Option γ → PMF β := fun outcome => outcome.elim (residual.bind second) second
  have target : ν.bind second = μ.bind fun a => joined (decode a) := by
    rw [← rebuilt, PMF.bind_bind, PMF.bind_map]
    refine bind_congr_on_support _ fun a _ => ?_
    simp only [Function.comp_apply, joined]
    cases decode a with
    | none => rfl
    | some c => exact PMF.pure_bind _ _
  let total : α → ℝ := fun a => match decode a with
    | none => 1
    | some _ => error a
  have totalBounded (a : α) : |total a| ≤ 1 := by
    simp only [total]
    split
    · simp
    · rw [abs_of_nonneg (errorNonneg a)]
      exact errorAtMostOne a
  have closeAll := WithinTV.bind_right_expect μ (first := first)
    (second := fun a => joined (decode a)) total
    (payoffIntegrable_of_bounded μ _ (C := 1) totalBounded) fun a member => by
      simp only [total, joined]
      cases outcome : decode a with
      | none => exact withinTV_one _ _
      | some c => exact close a member c outcome
  rw [target]
  refine closeAll.mono (le_of_eq ?_)
  have failure : ((μ.map decode) none).toReal =
      expect μ fun a => if (decode a).isSome then 0 else 1 := by
    rw [toReal_map_apply]
    refine expect_congr_on_support fun a _ => ?_
    cases decode a <;> simp
  rw [failure, ← expect_add (payoffIntegrable_of_bounded μ _ (C := 1) fun a => by
      split <;> simp)
    (payoffIntegrable_of_bounded μ _ (C := 1) fun a => by
      split
      · rw [abs_of_nonneg (errorNonneg a)]
        exact errorAtMostOne a
      · simp)]
  refine expect_congr_on_support fun a _ => ?_
  simp only [total]
  cases decode a <;> simp

end PMF
