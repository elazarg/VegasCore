/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.Domination
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Math.Probability.ExpectationMixture
import GameTheory.Math.Probability.Support

/-! # Expectations of composed laws -/

noncomputable section

namespace GameTheory.Math.Probability

/-- Cross-support payoff order is preserved by taking both expectations.
The laws and their carriers need not be finite or related by a coupling. -/
theorem expect_le_expect_of_support_order {α β : Type*}
    (left : PMF α) (right : PMF β) (first : α → ℝ) (second : β → ℝ)
    (leftIntegrable : PayoffIntegrable left first)
    (rightIntegrable : PayoffIntegrable right second)
    (ordered : ∀ a ∈ left.support, ∀ b ∈ right.support, second b ≤ first a) :
    expect right second ≤ expect left first := by
  have averaged := expect_mono (μ := left)
    (f := fun _ => expect right second) (g := first)
    (fun a supported => expect_le_const right second rightIntegrable (first a)
      (ordered a supported)) (payoffIntegrable_constant left _) leftIntegrable
  simpa only [expect_constant] using averaged

/-- A uniform cross-support payoff error contributes the same error after
averaging, with no assumption on the sizes of the supports. -/
theorem expect_le_expect_add_of_support_order {α β : Type*}
    (left : PMF α) (right : PMF β) (first : α → ℝ) (second : β → ℝ)
    (leftIntegrable : PayoffIntegrable left first)
    (rightIntegrable : PayoffIntegrable right second) (slack : ℝ)
    (ordered : ∀ a ∈ left.support, ∀ b ∈ right.support, second b ≤ first a + slack) :
    expect right second ≤ expect left first + slack := by
  have comparison := expect_le_expect_of_support_order left right (fun a => first a + slack)
    second (payoffIntegrable_add leftIntegrable (payoffIntegrable_constant left slack))
    rightIntegrable ordered
  simpa only [expect_add leftIntegrable (payoffIntegrable_constant left slack),
    expect_constant] using comparison

/-- Supported kernel domination composes with domination of the initial law. -/
theorem bind_supported_domination {α β : Type*}
    (source target : PMF α) (sourceStep targetStep : α → PMF β)
    (initialFactor stepFactor : ℝ) (initialNonnegative : 0 ≤ initialFactor)
    (initialLower : ∀ value, initialFactor * (source value).toReal ≤ (target value).toReal)
    (stepLower : ∀ prior ∈ source.support, ∀ value,
      stepFactor * (sourceStep prior value).toReal ≤ (targetStep prior value).toReal)
    (value : β) :
    (initialFactor * stepFactor) * ((source.bind sourceStep) value).toReal ≤
      ((target.bind targetStep) value).toReal := by
  rw [toReal_bind_apply, toReal_bind_apply]
  calc
    _ = initialFactor * expect source
        (fun prior => stepFactor * (sourceStep prior value).toReal) := by
      rw [expect_const_mul]
      ring
    _ ≤ initialFactor * expect source (fun prior => (targetStep prior value).toReal) :=
      mul_le_mul_of_nonneg_left (expect_mono
        (fun prior supported => stepLower prior supported value)
        (payoffIntegrable_of_bounded _ _ (C := |stepFactor|) fun prior => by
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_of_le_one_right (abs_nonneg _) (pmf_toReal_apply_le_one _ _))
        (payoffIntegrable_toReal_apply source targetStep value)) initialNonnegative
    _ ≤ expect target (fun prior => (targetStep prior value).toReal) :=
      mul_expect_le_of_prob_le source target initialFactor initialLower _
        (fun _ => ENNReal.toReal_nonneg) (payoffIntegrable_toReal_apply target targetStep value)


/-- The event masses of a kernel are integrable against every law. -/
theorem payoffIntegrable_toReal_toOuterMeasure {α β : Type*} (μ : PMF α) (f : α → PMF β)
    (event : Set β) : PayoffIntegrable μ fun a => ((f a).toOuterMeasure event).toReal :=
  payoffIntegrable_of_bounded μ _ (C := 1) fun a => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using outerMeasure_le_one (f a) event)

/-- An event's indicator is integrable against every law. The decision
procedure is implicit so that any instance at the use site matches. -/
theorem payoffIntegrable_ite_one_zero {α : Type*} (μ : PMF α) (p : α → Prop)
    {decide : DecidablePred p} : PayoffIntegrable μ fun a => if p a then (1 : ℝ) else 0 :=
  payoffIntegrable_of_bounded μ _ (C := 1) fun a => by split <;> norm_num

open Classical in
/-- The real mass of an atom of a pushforward is the probability of its fiber. -/
theorem toReal_map_apply {α β : Type*} (f : α → β) (μ : PMF α) (b : β) :
    ((μ.map f) b).toReal = expect μ fun a => if b = f a then 1 else 0 := by
  rw [← PMF.bind_pure_comp, toReal_bind_apply]
  apply expect_congr_on_support
  intro a _
  by_cases same : b = f a <;> simp [PMF.pure_apply, same]

/-- A payoff supported on one point has that point's weighted value. -/
theorem expect_ite_eq {α : Type*} [DecidableEq α] (μ : PMF α) (a : α) (c : ℝ) :
    (expect μ fun x => if a = x then c else 0) = (μ a).toReal * c := by
  unfold expect
  rw [tsum_eq_single a fun b different => by simp [Ne.symm different]]
  simp

/-- On a finite carrier the mixture rule needs no integrability premise. -/
theorem expect_mix_of_finite {α : Type*} [Finite α] (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ ν : PMF α) (f : α → ℝ) :
    expect (mix t h0 h1 μ ν) f = t * expect μ f + (1 - t) * expect ν f :=
  expect_mix t h0 h1 μ ν f (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

/-- On a finite carrier the tower rule needs no integrability premise. -/
theorem expect_bind_of_finite {α β : Type*} [Finite β] (p : PMF α) (q : α → PMF β)
    (f : β → ℝ) : expect (p.bind q) f = expect p (fun a => expect (q a) f) :=
  expect_bind_tower p q f (payoffIntegrable_of_finite _ _)

/-- On a finite carrier expectation is additive without integrability premises. -/
theorem expect_add_of_finite {α : Type*} [Finite α] (μ : PMF α) (f g : α → ℝ) :
    expect μ (fun a => f a + g a) = expect μ f + expect μ g :=
  expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

/-- A constant factor on the right leaves the expectation. -/
theorem expect_mul_const {α : Type*} (μ : PMF α) (f : α → ℝ) (c : ℝ) :
    expect μ (fun a => f a * c) = expect μ f * c := by
  simp_rw [mul_comm _ c]
  rw [expect_const_mul, mul_comm]

/-- A finitely supported law's expectation is a finite sum over its support. -/
theorem expect_eq_sum_of_support_finite {α : Type*} (μ : PMF α) (finite : μ.support.Finite)
    (f : α → ℝ) : expect μ f = ∑ a ∈ finite.toFinset, (μ a).toReal * f a := by
  unfold expect
  apply tsum_eq_sum
  intro a absent
  rw [Set.Finite.mem_toFinset, PMF.mem_support_iff, not_not] at absent
  simp [absent]

/-- Expectations commute when the outer law is finitely supported and the inner
integrand is integrable at every supported outer point; the inner law may have
infinite support. -/
theorem expect_comm_of_support_finite_left {α β : Type*} (μ : PMF α) (ν : PMF β)
    (μFinite : μ.support.Finite) (g : α → β → ℝ)
    (integrable : ∀ a ∈ μ.support, PayoffIntegrable ν (g a)) :
    expect μ (fun a => expect ν (fun b => g a b)) =
      expect ν (fun b => expect μ (fun a => g a b)) := by
  simp_rw [expect_eq_sum_of_support_finite μ μFinite, ← Finset.sum_coe_sort μFinite.toFinset]
  rw [expect_sum ν (fun a : μFinite.toFinset => fun b => (μ a).toReal * g a b) fun a =>
    payoffIntegrable_const_mul (integrable a (μFinite.mem_toFinset.mp a.2))]
  simp_rw [expect_const_mul]

/-- Independent expectations under finitely supported laws commute. -/
theorem expect_comm_of_support_finite {α β : Type*} (μ : PMF α) (ν : PMF β)
    (μFinite : μ.support.Finite) (νFinite : ν.support.Finite) (g : α → β → ℝ) :
    expect μ (fun a => expect ν (fun b => g a b)) =
      expect ν (fun b => expect μ (fun a => g a b)) := by
  simp_rw [expect_eq_sum_of_support_finite _ μFinite, expect_eq_sum_of_support_finite _ νFinite,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

end GameTheory.Math.Probability
