/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ExpectationComposition
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Math.Probability.ExpectationAlgebra

/-! # Approximately lumpable kernels

Two laws are `δ`-close on unit payoffs when every payoff with values in
`[0, 1]` has expectations within `δ` under them
(`GameTheory.Math.Probability.UnitClose`). Suppose a kernel keeps a set of
states, and from each state of the set its law, read through a map `φ`, is
`δ`-close on unit payoffs to a kernel on the images applied at the image. Then
`n` steps of the kernel from a state of the set, read through `φ`, are
`n δ`-close to `n` steps of the image kernel from the image
(`GameTheory.Math.Probability.iterate_bind_map_unitClose`). With `δ = 0` the map
lumps the kernel exactly.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- Two laws whose expectations of every payoff with values in `[0, 1]` are
within `δ`. -/
def UnitClose {α : Type*} (δ : ℝ) (μ ν : PMF α) : Prop :=
  ∀ f : α → ℝ, (∀ a, 0 ≤ f a ∧ f a ≤ 1) → |expect μ f - expect ν f| ≤ δ

theorem expect_mem_unit {α : Type*} (μ : PMF α) (f : α → ℝ) (unit : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ expect μ f ∧ expect μ f ≤ 1 := by
  have bounded : ∀ a, |f a| ≤ 1 := fun a =>
    abs_le.mpr ⟨by linarith [(unit a).1], (unit a).2⟩
  exact ⟨expect_nonneg μ f fun a _ => (unit a).1,
    expect_le_const μ f (payoffIntegrable_of_bounded μ f bounded) 1 fun a _ => (unit a).2⟩

/-- Unit payoffs within `δ` of each other on a law's support have expectations
within `δ`. -/
theorem abs_expect_sub_le_of_unit {α : Type*} (μ : PMF α) (f g : α → ℝ)
    (unitF : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (unitG : ∀ a, 0 ≤ g a ∧ g a ≤ 1) (δ : ℝ)
    (near : ∀ a ∈ μ.support, |f a - g a| ≤ δ) :
    |expect μ f - expect μ g| ≤ δ := by
  have boundF : ∀ a, |f a| ≤ 1 := fun a => abs_le.mpr ⟨by linarith [(unitF a).1], (unitF a).2⟩
  have boundG : ∀ a, |g a| ≤ 1 := fun a => abs_le.mpr ⟨by linarith [(unitG a).1], (unitG a).2⟩
  have integrableF := payoffIntegrable_of_bounded μ f boundF
  have integrableG := payoffIntegrable_of_bounded μ g boundG
  have difference : PayoffIntegrable μ (fun a => f a - g a) :=
    payoffIntegrable_of_bounded μ _ (C := 2) fun a => by
      have := abs_sub (f a) (g a)
      linarith [boundF a, boundG a]
  rw [← expect_sub integrableF integrableG]
  have upper := expect_le_const μ _ difference δ fun a supported =>
    (abs_le.mp (near a supported)).2
  have lower := expect_mono (μ := μ) (f := fun _ => -δ)
    (fun a supported => (abs_le.mp (near a supported)).1)
    (payoffIntegrable_constant μ _) difference
  rw [expect_constant] at lower
  exact abs_le.mpr ⟨lower, upper⟩

/-- **Approximate lumping.** If a kernel keeps a set, and from each of its
states the kernel read through `φ` is `δ`-close on unit payoffs to the image
kernel at the image, then `n` steps read through `φ` are `n δ`-close to `n`
steps of the image kernel. -/
theorem iterate_bind_map_unitClose {S Y : Type*} (kernel : S → PMF S) (φ : S → Y)
    (image : Y → PMF Y) (keep : Set S) (δ : ℝ)
    (kept : ∀ state ∈ keep, ∀ next ∈ (kernel state).support, next ∈ keep)
    (close : ∀ state ∈ keep, UnitClose δ ((kernel state).map φ) (image (φ state))) :
    ∀ (n : ℕ) (state : S), state ∈ keep →
      (∀ next ∈ ((fun law => law.bind kernel)^[n] (PMF.pure state)).support, next ∈ keep) ∧
      UnitClose (n * δ) (((fun law => law.bind kernel)^[n] (PMF.pure state)).map φ)
        ((fun law => law.bind image)^[n] (PMF.pure (φ state))) := by
  intro n state start
  induction n with
  | zero =>
      refine ⟨fun next member => by
        simp only [Function.iterate_zero_apply, PMF.mem_support_pure_iff] at member
        rw [member]
        exact start, fun f _ => ?_⟩
      simp only [Function.iterate_zero_apply, PMF.pure_map, Nat.cast_zero, zero_mul, sub_self,
        abs_zero, le_refl]
  | succ n ih =>
      obtain ⟨inside, near⟩ := ih
      set law := (fun law => law.bind kernel)^[n] (PMF.pure state)
      set imageLaw := (fun law => law.bind image)^[n] (PMF.pure (φ state))
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨fun next member => ?_, fun f unit => ?_⟩
      · rw [PMF.mem_support_bind_iff] at member
        obtain ⟨previous, previousMember, nextMember⟩ := member
        exact kept previous (inside previous previousMember) next nextMember
      · have boundF : ∀ y, |f y| ≤ 1 := fun y =>
          abs_le.mpr ⟨by linarith [(unit y).1], (unit y).2⟩
        let continued : Y → ℝ := fun y => expect (image y) f
        have unitContinued : ∀ y, 0 ≤ continued y ∧ continued y ≤ 1 := fun y =>
          expect_mem_unit (image y) f unit
        have stepped : expect ((law.bind kernel).map φ) f =
            expect law (fun s => expect ((kernel s).map φ) f) := by
          rw [expect_map, expect_bind_tower_bounded law kernel (f ∘ φ)
            (fun s => boundF (φ s))]
          exact expect_congr_on_support fun s _ => (expect_map φ (kernel s) f).symm
        have first : |expect law (fun s => expect ((kernel s).map φ) f) -
            expect law (fun s => continued (φ s))| ≤ δ :=
          abs_expect_sub_le_of_unit law _ _ (fun s => expect_mem_unit _ f unit)
            (fun s => unitContinued (φ s)) δ fun s supported =>
              close s (inside s supported) f unit
        have second : |expect (law.map φ) continued - expect imageLaw continued| ≤ n * δ :=
          near continued unitContinued
        rw [stepped, expect_bind_tower_bounded imageLaw image f boundF]
        rw [expect_map] at second
        have total := abs_sub_le (expect law (fun s => expect ((kernel s).map φ) f))
          (expect law (continued ∘ φ)) (expect imageLaw continued)
        push_cast
        calc _ ≤ _ := total
          _ ≤ δ + n * δ := add_le_add first second
          _ = (n + 1) * δ := by ring

end GameTheory.Math.Probability
