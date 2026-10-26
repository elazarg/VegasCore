/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support
import Mathlib.LinearAlgebra.Span.Basic

/-! # Signed observable moments under continuation kernels

A finite span transports expectations without identifying full laws. Propagation
through continuation kernels additionally requires explicit span closure under
both actual kernels, with the same coefficient matrix. No such closure follows
from equality of terminal moments alone.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- Checking initial expectations on generators checks their whole span.
Finiteness of the state carrier supplies the linearity guards. -/
theorem expect_eq_on_observable_span {State Index : Type*} [Finite State]
    (source target : PMF State) (basis : Index → State → ℝ)
    (moments : ∀ index, expect source (basis index) = expect target (basis index))
    {value : State → ℝ} (member : value ∈ Submodule.span ℝ (Set.range basis)) :
    expect source value = expect target value := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ member
  · rintro _ ⟨index, rfl⟩; exact moments index
  · change expect source (fun _ => 0) = expect target (fun _ => 0)
    rw [expect_zero, expect_zero]
  · intro first second _ _ firstEqual secondEqual
    change expect source (fun state => first state + second state) =
      expect target (fun state => first state + second state)
    rw [expect_add_of_finite, expect_add_of_finite, firstEqual, secondEqual]
  · intro scalar value _ equal
    change expect source (fun state => scalar * value state) =
      expect target (fun state => scalar * value state)
    rw [expect_const_mul, expect_const_mul, equal]

/-- Agreement on an integrable finite observable basis identifies the means
of represented payoffs, even on different hidden carriers. -/
theorem expect_eq_of_observable_span {Source Target Index : Type*} [Fintype Index]
    (source : PMF Source) (target : PMF Target)
    (sourceBasis : Index → Source → ℝ) (targetBasis : Index → Target → ℝ)
    (coefficient : Index → ℝ)
    (sourceIntegrable : ∀ i, PayoffIntegrable source (sourceBasis i))
    (targetIntegrable : ∀ i, PayoffIntegrable target (targetBasis i))
    (sourceValue : Source → ℝ) (targetValue : Target → ℝ)
    (sourceRepresentation : ∀ s ∈ source.support,
      sourceValue s = ∑ i, coefficient i * sourceBasis i s)
    (targetRepresentation : ∀ t ∈ target.support,
      targetValue t = ∑ i, coefficient i * targetBasis i t)
    (moments : ∀ i, expect source (sourceBasis i) = expect target (targetBasis i)) :
    PayoffIntegrable source sourceValue ∧ PayoffIntegrable target targetValue ∧
      expect source sourceValue = expect target targetValue := by
  obtain ⟨sourceValueIntegrable, sourceMean⟩ := expect_eq_sum_on_support source
    (fun i s => coefficient i * sourceBasis i s) sourceValue
    (fun i => payoffIntegrable_const_mul (sourceIntegrable i)) sourceRepresentation
  obtain ⟨targetValueIntegrable, targetMean⟩ := expect_eq_sum_on_support target
    (fun i t => coefficient i * targetBasis i t) targetValue
    (fun i => payoffIntegrable_const_mul (targetIntegrable i)) targetRepresentation
  refine ⟨sourceValueIntegrable, targetValueIntegrable, ?_⟩
  rw [sourceMean, targetMean]
  simp only [expect_const_mul, moments]

/-- Moment errors control a selected represented payoff by the coefficient
weighted sum. The integration conditions are inherited by both represented payoffs. -/
theorem abs_expect_sub_le_of_observable_span {Source Target Index : Type*} [Fintype Index]
    (source : PMF Source) (target : PMF Target)
    (sourceBasis : Index → Source → ℝ) (targetBasis : Index → Target → ℝ)
    (coefficient : Index → ℝ)
    (sourceIntegrable : ∀ i, PayoffIntegrable source (sourceBasis i))
    (targetIntegrable : ∀ i, PayoffIntegrable target (targetBasis i))
    (sourceValue : Source → ℝ) (targetValue : Target → ℝ)
    (sourceRepresentation : ∀ s ∈ source.support,
      sourceValue s = ∑ i, coefficient i * sourceBasis i s)
    (targetRepresentation : ∀ t ∈ target.support,
      targetValue t = ∑ i, coefficient i * targetBasis i t)
    (error : Index → ℝ)
    (moments : ∀ i, |expect source (sourceBasis i) - expect target (targetBasis i)| ≤ error i) :
    |expect source sourceValue - expect target targetValue| ≤
      ∑ i, |coefficient i| * error i := by
  have sourceMean := (expect_eq_sum_on_support source
    (fun i s => coefficient i * sourceBasis i s) sourceValue
    (fun i => payoffIntegrable_const_mul (sourceIntegrable i)) sourceRepresentation).2
  have targetMean := (expect_eq_sum_on_support target
    (fun i t => coefficient i * targetBasis i t) targetValue
    (fun i => payoffIntegrable_const_mul (targetIntegrable i)) targetRepresentation).2
  rw [sourceMean, targetMean, ← Finset.sum_sub_distrib]
  simp only [expect_const_mul, ← mul_sub]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (moments i) (abs_nonneg _))

/-- A common closure matrix for two actual continuation kernels transports
all basis moments through one step. The tower law's guards are explicit. -/
theorem expect_bind_eq_of_closed_observables {Source Target Index : Type*} [Fintype Index]
    (source : PMF Source) (target : PMF Target)
    (sourceStep : Source → PMF Source) (targetStep : Target → PMF Target)
    (sourceBasis : Index → Source → ℝ) (targetBasis : Index → Target → ℝ)
    (coefficient : Index → Index → ℝ)
    (sourceIntegrable : ∀ i, PayoffIntegrable source (sourceBasis i))
    (targetIntegrable : ∀ i, PayoffIntegrable target (targetBasis i))
    (sourceNextIntegrable : ∀ i, PayoffIntegrable (source.bind sourceStep) (sourceBasis i))
    (targetNextIntegrable : ∀ i, PayoffIntegrable (target.bind targetStep) (targetBasis i))
    (sourceClosed : ∀ i s, s ∈ source.support →
      expect (sourceStep s) (sourceBasis i) = ∑ j, coefficient i j * sourceBasis j s)
    (targetClosed : ∀ i t, t ∈ target.support →
      expect (targetStep t) (targetBasis i) = ∑ j, coefficient i j * targetBasis j t)
    (moments : ∀ i, expect source (sourceBasis i) = expect target (targetBasis i)) :
    ∀ i, expect (source.bind sourceStep) (sourceBasis i) =
      expect (target.bind targetStep) (targetBasis i) := by
  intro i
  rw [expect_bind_tower source sourceStep _ (sourceNextIntegrable i),
    expect_bind_tower target targetStep _ (targetNextIntegrable i)]
  exact (expect_eq_of_observable_span source target sourceBasis targetBasis (coefficient i)
    sourceIntegrable targetIntegrable _ _ (sourceClosed i) (targetClosed i) moments).2.2

/-- Bounded basis observables with a common global continuation-closure matrix
keep matching moments along the existing iterated-PMF-bind evaluator. This says
nothing about observables outside that closed span or equality of full laws. -/
theorem expect_iterate_eq_of_closed_observables {Source Target Index : Type*} [Fintype Index]
    (source : PMF Source) (target : PMF Target)
    (sourceStep : Source → PMF Source) (targetStep : Target → PMF Target)
    (sourceBasis : Index → Source → ℝ) (targetBasis : Index → Target → ℝ)
    (coefficient : Index → Index → ℝ) (sourceBound targetBound : Index → ℝ)
    (sourceBounded : ∀ i s, |sourceBasis i s| ≤ sourceBound i)
    (targetBounded : ∀ i t, |targetBasis i t| ≤ targetBound i)
    (sourceClosed : ∀ i s,
      expect (sourceStep s) (sourceBasis i) = ∑ j, coefficient i j * sourceBasis j s)
    (targetClosed : ∀ i t,
      expect (targetStep t) (targetBasis i) = ∑ j, coefficient i j * targetBasis j t)
    (moments : ∀ i, expect source (sourceBasis i) = expect target (targetBasis i)) :
    ∀ count i,
      expect ((fun law => law.bind sourceStep)^[count] source) (sourceBasis i) =
        expect ((fun law => law.bind targetStep)^[count] target) (targetBasis i) := by
  intro count
  induction count with
  | zero => exact moments
  | succ count ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact expect_bind_eq_of_closed_observables _ _ sourceStep targetStep sourceBasis targetBasis
        coefficient
        (fun i => payoffIntegrable_of_bounded _ _ (sourceBounded i))
        (fun i => payoffIntegrable_of_bounded _ _ (targetBounded i))
        (fun i => payoffIntegrable_of_bounded _ _ (sourceBounded i))
        (fun i => payoffIntegrable_of_bounded _ _ (targetBounded i))
        (fun i s _ => sourceClosed i s) (fun i t _ => targetClosed i t) ih

end GameTheory.Math.Probability
