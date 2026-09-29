/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationMap

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
