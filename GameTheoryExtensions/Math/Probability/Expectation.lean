/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Math.Probability.ExpectationMixture

/-! # Expectations of composed laws -/

noncomputable section

namespace GameTheory.Math.Probability

/-- Real atom masses are at most one. -/
theorem pmf_toReal_apply_le_one {α : Type*} (μ : PMF α) (a : α) : (μ a).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using μ.coe_le_one a)

/-- The atom masses of a kernel are integrable against every law. -/
theorem payoffIntegrable_toReal_apply {α β : Type*} (μ : PMF α) (f : α → PMF β) (b : β) :
    PayoffIntegrable μ fun a => ((f a) b).toReal :=
  payoffIntegrable_of_bounded μ _ (C := 1) fun a => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact pmf_toReal_apply_le_one _ _

/-- The real mass of an atom of a bind is the expected real mass of that atom
under the branches. -/
theorem toReal_bind_apply {α β : Type*} (μ : PMF α) (f : α → PMF β) (b : β) :
    ((μ.bind f) b).toReal = expect μ fun a => ((f a) b).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq fun a =>
    ENNReal.mul_ne_top (μ.apply_ne_top a) ((f a).apply_ne_top b)]
  simp only [ENNReal.toReal_mul, expect]

/-- A mixture integrates the mass of each branch's event. -/
theorem toReal_toOuterMeasure_bind {α β : Type*} (μ : PMF α) (f : α → PMF β) (event : Set β) :
    ((μ.bind f).toOuterMeasure event).toReal =
      expect μ fun a => ((f a).toOuterMeasure event).toReal := by
  rw [PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq fun a =>
    ENNReal.mul_ne_top (μ.apply_ne_top a) (outerMeasure_ne_top (f a) event)]
  simp only [ENNReal.toReal_mul, expect]

/-- Branchwise agreement of readouts transports an expectation over a mixture.
No integrability is needed: both sides are the expectation of one readout law. -/
theorem expect_bind_readout_congr {α β γ δ : Type*} (μ : PMF α) (f : α → PMF β)
    (g : α → PMF γ) (u : β → δ) (v : γ → δ) (payoff : δ → ℝ)
    (same : ∀ a ∈ μ.support, (f a).map u = (g a).map v) :
    expect (μ.bind f) (fun b => payoff (u b)) = expect (μ.bind g) (fun c => payoff (v c)) := by
  have readout : (μ.bind f).map u = (μ.bind g).map v := by
    rw [PMF.map_bind, PMF.map_bind]
    exact bind_congr_on_support μ same
  have first := expect_map u (μ.bind f) payoff
  have second := expect_map v (μ.bind g) payoff
  rw [readout, second] at first
  exact first.symm

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

/-- A payoff dominated on the support by an integrable one is integrable. -/
theorem payoffIntegrable_of_abs_le_on_support {α : Type*} {μ : PMF α} {f g : α → ℝ}
    (hg : PayoffIntegrable μ g) (bound : ∀ a ∈ μ.support, |f a| ≤ |g a|) :
    PayoffIntegrable μ f := by
  unfold PayoffIntegrable at hg ⊢
  refine Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
    (fun a => ?_) hg
  by_cases supported : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (bound a supported) ENNReal.toReal_nonneg
  · simp [(PMF.apply_eq_zero_iff μ a).mpr supported]

/-- A kernel whose values stay within a bounded offset of an integrable outer
payoff has an integrable bind. -/
theorem payoffIntegrable_bind_of_abs_le {α β : Type*} (p : PMF α) (q : α → PMF β)
    (f : β → ℝ) (g : α → ℝ) (offset : ℝ) (hg : PayoffIntegrable p g)
    (bound : ∀ a ∈ p.support, ∀ b ∈ (q a).support, |f b| ≤ |g a| + offset) :
    PayoffIntegrable (p.bind q) f := by
  rw [← bindPairLaw_map_snd, payoffIntegrable_map_iff]
  have absolute : PayoffIntegrable ((bindPairLaw p q).map Prod.fst) (fun a => |g a|) := by
    rw [bindPairLaw_map_fst]
    simpa only [PayoffIntegrable, abs_abs] using hg
  have outer : PayoffIntegrable (bindPairLaw p q) (fun pair => |g pair.1| + |offset|) := by
    have lifted := (payoffIntegrable_map_iff _ _ _).mp absolute
    exact payoffIntegrable_add lifted (payoffIntegrable_constant _ |offset|)
  apply payoffIntegrable_of_abs_le_on_support outer
  rintro ⟨a, b⟩ supported
  rw [PMF.mem_support_iff, bindPairLaw_apply, mul_ne_zero_iff] at supported
  have within := bound a ((PMF.mem_support_iff _ _).mpr supported.1) b
    ((PMF.mem_support_iff _ _).mpr supported.2)
  change |f b| ≤ |(|g a| + |offset|)|
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (g a)) (abs_nonneg offset))]
  exact within.trans (add_le_add le_rfl (le_abs_self offset))

/-- On a finite carrier the tower rule needs no integrability premise. -/
theorem expect_bind_of_finite {α β : Type*} [Finite β] (p : PMF α) (q : α → PMF β)
    (f : β → ℝ) : expect (p.bind q) f = expect p (fun a => expect (q a) f) :=
  expect_bind_tower p q f (payoffIntegrable_of_finite _ _)

/-- A payoff read through a finite summary is integrable under every law, even
on an infinite carrier. -/
theorem payoffIntegrable_of_finite_summary {α β : Type*} [Finite β] (μ : PMF α)
    (summary : α → β) (g : β → ℝ) : PayoffIntegrable μ (fun a => g (summary a)) :=
  (payoffIntegrable_map_iff summary μ g).mp (payoffIntegrable_of_finite _ _)

/-- Expected values of a uniformly bounded payoff are integrable against every law. -/
theorem payoffIntegrable_expect_of_bounded {α β : Type*} (μ : PMF α) (kernel : α → PMF β)
    (f : β → ℝ) {C : ℝ} (nonnegative : 0 ≤ C) (bound : ∀ b, |f b| ≤ C) :
    PayoffIntegrable μ (fun a => expect (kernel a) f) :=
  payoffIntegrable_of_bounded _ _ fun _ => expect_abs_le_of_bounded nonnegative bound

/-- Expected values of a payoff read through a finite summary are bounded,
hence integrable against every law. -/
theorem payoffIntegrable_expect_of_finite_summary {α β γ : Type*} [Finite γ] (μ : PMF α)
    (kernel : α → PMF β) (summary : β → γ) (g : γ → ℝ) :
    PayoffIntegrable μ (fun a => expect (kernel a) (fun b => g (summary b))) := by
  obtain ⟨C, bound⟩ := (Set.finite_range fun c => |g c|).bddAbove
  exact payoffIntegrable_expect_of_bounded _ _ _ (le_max_right C 0) fun b =>
    (bound ⟨summary b, rfl⟩).trans (le_max_left _ _)

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

/-- Two laws that bind one mixture into the prescribed and alternative laws of
its components have, for every integrable utility, the mixture's average gain
as their gain. -/
theorem expect_sub_eq_of_eq_bind {γ δ : Type*} (mixture : PMF γ)
    (prescribed alternative : PMF δ) (componentPrescribed componentAlternative : γ → PMF δ)
    (prescribedEq : prescribed = mixture.bind componentPrescribed)
    (alternativeEq : alternative = mixture.bind componentAlternative) (utility : δ → ℝ)
    (prescribedIntegrable : PayoffIntegrable prescribed utility)
    (alternativeIntegrable : PayoffIntegrable alternative utility) :
    expect alternative utility - expect prescribed utility =
      expect mixture (fun component =>
        expect (componentAlternative component) utility -
          expect (componentPrescribed component) utility) := by
  subst prescribedEq alternativeEq
  rw [expect_bind_tower _ _ _ prescribedIntegrable, expect_bind_tower _ _ _ alternativeIntegrable,
    expect_sub
      (payoffIntegrable_bind_conditionalExpectation _ _ _ alternativeIntegrable)
      (payoffIntegrable_bind_conditionalExpectation _ _ _ prescribedIntegrable)]

end GameTheory.Math.Probability
