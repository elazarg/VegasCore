/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Approximately lumpable kernels

Suppose a kernel keeps a set of states, and from each state of the set its law,
read through a map `φ`, is
within `δ` in total variation to a kernel on the images applied at the image. Then
`n` steps of the kernel from a state of the set, read through `φ`, are
within `n δ` in total variation to `n` steps of the image kernel from the image
(`GameTheory.Math.Probability.iterate_bind_map_withinTV`). With `δ = 0` the map
lumps the kernel exactly.
-/

noncomputable section

namespace GameTheory.Math.Probability

theorem expect_mem_unit {α : Type*} (μ : PMF α) (f : α → ℝ) (unit : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ expect μ f ∧ expect μ f ≤ 1 := by
  have bounded : ∀ a, |f a| ≤ 1 := fun a =>
    abs_le.mpr ⟨by linarith [(unit a).1], (unit a).2⟩
  exact ⟨expect_nonneg μ f fun a _ => (unit a).1,
    expect_le_const μ f (payoffIntegrable_of_bounded μ f bounded) 1 fun a _ => (unit a).2⟩

/-- **Approximate lumping.** If a kernel keeps a set, and from each of its
states the kernel read through `φ` is within `δ` in total variation to the image
kernel at the image, then `n` steps read through `φ` are within `n δ` in total variation to `n`
steps of the image kernel. -/
theorem iterate_bind_map_withinTV {S Y : Type*} (kernel : S → PMF S) (φ : S → Y)
    (image : Y → PMF Y) (keep : Set S) (δ : ℝ)
    (kept : ∀ state ∈ keep, ∀ next ∈ (kernel state).support, next ∈ keep)
    (close : ∀ state ∈ keep, PMF.WithinTV δ ((kernel state).map φ) (image (φ state))) :
    ∀ (n : ℕ) (state : S), state ∈ keep →
      (∀ next ∈ ((fun law => law.bind kernel)^[n] (PMF.pure state)).support, next ∈ keep) ∧
      PMF.WithinTV (n * δ) (((fun law => law.bind kernel)^[n] (PMF.pure state)).map φ)
        ((fun law => law.bind image)^[n] (PMF.pure (φ state))) := by
  intro n state start
  induction n with
  | zero =>
      refine ⟨fun next member => by
        simp only [Function.iterate_zero_apply, PMF.mem_support_pure_iff] at member
        rw [member]
        exact start, ?_⟩
      simpa only [Function.iterate_zero_apply, PMF.pure_map, Nat.cast_zero, zero_mul] using
        PMF.WithinTV.refl (PMF.pure (φ state))
  | succ n ih =>
      obtain ⟨inside, near⟩ := ih
      set law := (fun law => law.bind kernel)^[n] (PMF.pure state)
      set imageLaw := (fun law => law.bind image)^[n] (PMF.pure (φ state))
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨fun next member => ?_, ?_⟩
      · rw [PMF.mem_support_bind_iff] at member
        obtain ⟨previous, previousMember, nextMember⟩ := member
        exact kept previous (inside previous previousMember) next nextMember
      · have first : PMF.WithinTV δ ((law.bind kernel).map φ) ((law.map φ).bind image) := by
          rw [PMF.map_bind, PMF.bind_map]
          exact PMF.WithinTV.bind_right law fun point member => close point (inside point member)
        have combined := first.trans (near.bind_left image)
        convert combined using 1; push_cast; ring

/-- Expectation of a three-part decomposition with constant first two parts. -/
private theorem expect_three_parts {α : Type*} (μ : PMF α) (s r h : α → ℝ) (x y : ℝ)
    (boundS : ∀ a, |s a| ≤ 1) (boundR : ∀ a, |r a| ≤ 1) (boundH : ∀ a, |h a| ≤ 1) :
    expect μ (fun a => s a * x + (1 - s a - r a) * y + h a) =
      expect μ s * x + (1 - expect μ s - expect μ r) * y + expect μ h := by
  have integrableS := payoffIntegrable_of_bounded μ s boundS
  have integrableR := payoffIntegrable_of_bounded μ r boundR
  have integrableH := payoffIntegrable_of_bounded μ h boundH
  have integrableSX : PayoffIntegrable μ (fun a => s a * x) := by
    simpa only [mul_comm] using payoffIntegrable_const_mul (c := x) integrableS
  have integrableRest : PayoffIntegrable μ (fun a => (1 - s a - r a) * y) := by
    have sum : PayoffIntegrable μ (fun a => 1 - s a - r a) :=
      payoffIntegrable_sub (payoffIntegrable_sub (payoffIntegrable_constant μ 1) integrableS)
        integrableR
    simpa only [mul_comm] using payoffIntegrable_const_mul (c := y) sum
  rw [expect_add (payoffIntegrable_add integrableSX integrableRest) integrableH,
    expect_add integrableSX integrableRest]
  rw [expect_mul_const, expect_mul_const,
    expect_sub (payoffIntegrable_sub (payoffIntegrable_constant μ 1) integrableS) integrableR,
    expect_sub (payoffIntegrable_constant μ 1) integrableS, expect_constant]

/-- **A law with two outcomes up to a remainder.** If a law maps its silent
points to silentImage and its opening points to openImage, gives the silent
points mass within `δ₁` of the weight a Boolean law gives `true`, and leaves at
most `δ₂` outside both, then read through the map it is `(δ₁ + δ₂)`-close on
unit payoffs to the two-point law with that weight. -/
theorem withinTV_map_of_two_outcomes {α Y : Type*} (ν : PMF α) (F : α → Y)
    (silent opens : α → Prop) [DecidablePred silent] [DecidablePred opens]
    (silentImage openImage : Y) (weight : PMF Bool) (δ₁ δ₂ : ℝ)
    (silentEq : ∀ a ∈ ν.support, silent a → F a = silentImage)
    (openEq : ∀ a ∈ ν.support, ¬ silent a → opens a → F a = openImage)
    (silentMass : |expect ν (fun a => if silent a then 1 else 0) -
      expect weight (fun b => if b then 1 else 0)| ≤ δ₁)
    (remainder : expect ν (fun a => if silent a ∨ opens a then 0 else 1) ≤ δ₂) :
    PMF.WithinTV (δ₁ + δ₂) (ν.map F)
      (weight.map fun b => if b then silentImage else openImage) := by
  classical
  intro event
  let g : Y → ℝ := fun point => if point ∈ event then 1 else 0
  have unit : ∀ point, 0 ≤ g point ∧ g point ≤ 1 := fun point => by
    simp only [g]; split <;> norm_num
  rw [← expect_indicator, ← expect_indicator, expect_map, expect_map]
  change |expect ν (g ∘ F) - expect weight (g ∘ fun b =>
    if b then silentImage else openImage)| ≤ _
  set s : α → ℝ := fun a => if silent a then 1 else 0 with sEq
  set r : α → ℝ := fun a => if silent a ∨ opens a then 0 else 1 with rEq
  have boundS : ∀ a, |s a| ≤ 1 := fun a => by by_cases h : silent a <;> simp [s, h]
  have boundR : ∀ a, |r a| ≤ 1 := fun a => by by_cases h : silent a ∨ opens a <;> simp [r, h]
  have boundRG : ∀ a, |r a * g (F a)| ≤ 1 := fun a => by
    rw [abs_mul]
    have := abs_le.mpr ⟨by linarith [(unit (F a)).1], (unit (F a)).2⟩
    nlinarith [abs_nonneg (r a), abs_nonneg (g (F a)), boundR a]
  have decompose : expect ν (g ∘ F) =
      expect ν (fun a => s a * g silentImage + (1 - s a - r a) * g openImage +
        r a * g (F a)) := by
    apply expect_congr_on_support
    intro a supported
    by_cases isSilent : silent a
    · simp only [Function.comp, s, r, isSilent, silentEq a supported isSilent, true_or,
        ↓reduceIte]
      ring
    · by_cases isOpen : opens a
      · simp only [Function.comp, s, r, isSilent, isOpen, openEq a supported isSilent isOpen,
          or_true, ↓reduceIte]
        ring
      · simp only [Function.comp, s, r, isSilent, isOpen, or_self, ↓reduceIte]
        ring
  have weightDecompose : expect weight ((g ∘ fun b => if b then silentImage else openImage)) =
      expect weight (fun b => if b then 1 else 0) * g silentImage +
        (1 - expect weight (fun b => if b then 1 else 0) - expect weight (fun _ => 0)) *
          g openImage + expect weight (fun _ => 0) := by
    rw [← expect_three_parts weight _ _ _ _ _ (fun b => by cases b <;> simp)
      (fun _ => by simp) (fun _ => by simp)]
    apply expect_congr_on_support
    intro b _
    cases b <;> simp
  rw [decompose, weightDecompose, expect_three_parts ν s r _ _ _ boundS boundR boundRG,
    expect_zero]
  have restNonneg : 0 ≤ expect ν r := expect_nonneg ν r fun a _ => by
    by_cases h : silent a ∨ opens a <;> simp [r, h]
  have restGNonneg : 0 ≤ expect ν (fun a => r a * g (F a)) := expect_nonneg ν _ fun a _ =>
    mul_nonneg (by by_cases h : silent a ∨ opens a <;> simp [r, h]) (unit (F a)).1
  have restGLe : expect ν (fun a => r a * g (F a)) ≤ expect ν r := by
    apply expect_mono _ (payoffIntegrable_of_bounded ν _ boundRG)
      (payoffIntegrable_of_bounded ν r boundR)
    intro a _
    have : 0 ≤ r a := by by_cases h : silent a ∨ opens a <;> simp [r, h]
    have := (unit (F a)).2
    nlinarith
  have gap : |g silentImage - g openImage| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [(unit silentImage).1, (unit silentImage).2, (unit openImage).1,
      (unit openImage).2]
  have weightTerm : |(expect ν s - expect weight (fun b => if b then 1 else 0)) *
      (g silentImage - g openImage)| ≤ δ₁ := by
    rw [abs_mul]
    have := abs_nonneg (expect ν s - expect weight (fun b => if b then 1 else 0))
    calc _ ≤ |expect ν s - expect weight (fun b => if b then 1 else 0)| * 1 :=
          mul_le_mul_of_nonneg_left gap this
      _ ≤ δ₁ := by rw [mul_one]; exact silentMass
  have restTerm : |expect ν (fun a => r a * g (F a)) - g openImage * expect ν r| ≤ δ₂ := by
    have openUnit := unit openImage
    rw [abs_le]
    constructor <;> nlinarith
  calc _ = |(expect ν s - expect weight (fun b => if b then 1 else 0)) *
          (g silentImage - g openImage) +
        (expect ν (fun a => r a * g (F a)) - g openImage * expect ν r)| := by
        congr 1
        ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ δ₁ + δ₂ := add_le_add weightTerm restTerm



end GameTheory.Math.Probability
