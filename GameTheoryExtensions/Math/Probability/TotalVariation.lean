/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.OptionalDomination
import GameTheoryExtensions.Math.Probability.Domination

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

/-- A law containing a factor of another law loses at most the remaining mass. -/
theorem WithinTV.of_domination {α : Type*} (source target : PMF α)
    (factor : ℝ) (small : factor ≤ 1)
    (lower : ∀ value, factor * (source value).toReal ≤ (target value).toReal) :
    PMF.WithinTV (1 - factor) source target := by
  intro event
  have first := probOf_domination source target factor lower event
  have second := probOf_domination_excess source target factor lower event
  have atMostOne : (source.toOuterMeasure event).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one source event)
  have missing : (1 - factor) * (source.toOuterMeasure event).toReal ≤ 1 - factor :=
    mul_le_of_le_one_right (sub_nonneg.mpr small) atMostOne
  have scaled : factor * (source.toOuterMeasure event).toReal ≤
      (source.toOuterMeasure event).toReal :=
    mul_le_of_le_one_left ENNReal.toReal_nonneg small
  exact abs_le.mpr ⟨by linarith, by linarith⟩

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

/-- The existing interval estimate in both directions, with actual support
bounds supplying all expectation guards. -/
theorem WithinTV.abs_expect_sub_le_interval {Outcome : Type*} {first second : PMF Outcome}
    {error : ℝ} (close : WithinTV error first second)
    (value : Outcome → ℝ) (low range : ℝ)
    (bounded : ∀ outcome, outcome ∈ first.support ∨ outcome ∈ second.support →
      low ≤ value outcome ∧ value outcome ≤ low + range) :
    |GameTheory.Math.Probability.expect first value -
      GameTheory.Math.Probability.expect second value| ≤ error * range := by
  have forward := close.expect_sub_le value low range bounded
  have reverse := close.symm.expect_sub_le value low range
    (fun outcome member => bounded outcome member.symm)
  exact abs_le.mpr ⟨by linarith, forward⟩


/-- A common continuation kernel contracts total variation. -/
theorem WithinTV.bind_left {error : ℝ} {first second : PMF α}
    (close : WithinTV error first second) (kernel : α → PMF β) :
    WithinTV error (first.bind kernel) (second.bind kernel) := by
  intro event
  rw [toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind]
  have bound := close.abs_expect_sub_le_interval
    (fun point => ((kernel point).toOuterMeasure event).toReal) 0 1 (fun point _ =>
      ⟨ENNReal.toReal_nonneg, by
        simpa only [zero_add, abs_of_nonneg ENNReal.toReal_nonneg] using
          eventMass_bounded (kernel point) event⟩)
  simpa only [mul_one] using bound

/-- A lottery retaining one branch loses at most its missing mass. -/
theorem WithinTV.of_bind_point (timing : PMF ι) (index : ι)
    (branch : ι → PMF α) {error : ℝ} (mass : 1 - (timing index).toReal ≤ error) :
    WithinTV error (timing.bind branch) (branch index) := by
  have retained := WithinTV.of_domination (branch index) (timing.bind branch)
    (timing index).toReal (pmf_toReal_apply_le_one _ _) (fun outcome => by
      rw [← ENNReal.toReal_mul]
      apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
      rw [PMF.bind_apply]
      exact ENNReal.le_tsum (f := fun other => timing other * (branch other) outcome) index)
  exact retained.symm.mono mass

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

/-- Constant kernel errors are the constant case of expected kernel error. -/
theorem WithinTV.bind_right {error : ℝ} (law : PMF α) {first second : α → PMF β}
    (close : ∀ point ∈ law.support, WithinTV error (first point) (second point)) :
    WithinTV error (law.bind first) (law.bind second) := by
  simpa only [expect_constant] using WithinTV.bind_right_expect law (fun _ => error)
    (payoffIntegrable_constant law error) close

/-- A mixture stays within its extra component's weight of the retained law. -/
theorem WithinTV.mix_right (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (extra retained : PMF α) :
    WithinTV weight (mix weight nonnegative small extra retained) retained := by
  have bound := WithinTV.of_domination retained (mix weight nonnegative small extra retained)
    (1 - weight) (by linarith) (mix_retains_right ⟨weight, nonnegative, small⟩ extra retained)
  simpa only [sub_sub_cancel] using bound.symm

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

namespace GameTheory.Math.Probability

/-- Classification with arbitrary unclassified outputs contracts TV without
doubling the error. Classified outputs must have their declared actual image. -/
theorem withinTV_map_of_partial_classes {Source Class Output : Type*}
    (law : PMF Source) (read : Source → Output) (classify : Source → Option Class)
    (image : Class → Output) (reference : PMF Class) {error : ℝ}
    (classified : ∀ point ∈ law.support, ∀ classValue,
      classify point = some classValue → read point = image classValue)
    (close : PMF.WithinTV error (law.map classify) (reference.map some)) :
    PMF.WithinTV error (law.map read) (reference.map image) := by
  intro event
  let lower : Set (Option Class) := {value | value.elim False (fun c => image c ∈ event)}
  let upper : Set (Option Class) := {value | value.elim True (fun c => image c ∈ event)}
  have referenceLower : (reference.map some).toOuterMeasure lower =
      (reference.map image).toOuterMeasure event := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    rfl
  have referenceUpper : (reference.map some).toOuterMeasure upper =
      (reference.map image).toOuterMeasure event := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    rfl
  have below : (law.map classify).toOuterMeasure lower ≤ (law.map read).toOuterMeasure event := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    apply law.toOuterMeasure_mono
    rintro point ⟨member, supported⟩
    change read point ∈ event
    cases reading : classify point with
    | none => simp [lower, reading] at member
    | some classValue =>
        rw [classified point supported classValue reading]
        simpa [lower, reading] using member
  have above : (law.map read).toOuterMeasure event ≤ (law.map classify).toOuterMeasure upper := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    apply law.toOuterMeasure_mono
    rintro point ⟨member, supported⟩
    cases reading : classify point with
    | none => simp [upper, reading]
    | some classValue =>
        change (classify point).elim True (fun c => image c ∈ event)
        rw [reading, Option.elim_some, ← classified point supported classValue reading]
        exact member
  have belowReal := ENNReal.toReal_mono (outerMeasure_ne_top (law.map read) event) below
  have aboveReal := ENNReal.toReal_mono (outerMeasure_ne_top (law.map classify) upper) above
  have lowerBound := (abs_le.mp (close lower)).1
  have upperBound := (abs_le.mp (close upper)).2
  rw [referenceLower] at lowerBound
  rw [referenceUpper] at upperBound
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end GameTheory.Math.Probability
