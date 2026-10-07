/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Conditioning on survival

A law on points, some of which survive, is the mixture of its survivors,
conditioned on survival, weighted by their mass
(`GameTheory.Math.Probability.bind_apply_eq_mass_mul_filter`). When the
surviving part of a joint law of a state and a noise factors through a kernel of
an observation of the state that may also report that nothing survives, the
survivors conditioned on survival have the noise of the kernel conditioned on
survival (`GameTheory.Math.Probability.filter_map_factor`), and their states
weighted by the surviving mass are dominated by the law of the state
(`GameTheory.Math.Probability.filter_marginal_le`).
-/

noncomputable section

namespace GameTheory.Math.Probability

open scoped ENNReal

variable {α β γ W : Type*}

/-- The mass of a set times the law conditioned on it is the law restricted to
it. -/
theorem filter_mass_mul (law : PMF α) (event : Set α) (present : ∃ a ∈ event, a ∈ law.support)
    (a : α) :
    (∑' x, event.indicator law x) * law.filter event present a = event.indicator law a := by
  rw [PMF.filter_apply, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by simpa using present)
    (law.tsum_coe_indicator_ne_top event), mul_one]

/-- **A law is its conditioned survivors, weighted by their mass,** at every
outcome only survivors reach. -/
theorem bind_apply_eq_mass_mul_filter (law : PMF α) (event : Set α)
    (present : ∃ a ∈ event, a ∈ law.support) (kernel : α → PMF β) (b : β)
    (outside : ∀ a ∈ law.support, a ∉ event → kernel a b = 0) :
    (law.bind kernel) b =
      (∑' x, event.indicator law x) * (law.filter event present).bind kernel b := by
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  congr 1
  funext a
  rw [← mul_assoc, filter_mass_mul]
  by_cases member : a ∈ event
  · rw [Set.indicator_of_mem member]
  · rw [Set.indicator_of_notMem member, zero_mul]
    by_cases supported : a ∈ law.support
    · rw [outside a supported member, mul_zero]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul]

/-- The mass of the present values of a law on optional values. -/
def presentMass (law : PMF (Option β)) : ℝ≥0∞ := ∑' b, law (some b)

theorem presentMass_le_one (law : PMF (Option β)) : presentMass law ≤ 1 :=
  (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective β) law).trans
    law.tsum_coe.le

/-- The law of the present values, conditioned on presence; `fallback` when
nothing is present. -/
def presentConditional (law : PMF (Option β)) (fallback : PMF β) : PMF β :=
  if present : presentMass law ≠ 0 then
    PMF.normalize (fun b => law (some b)) present
      (ne_top_of_le_ne_top ENNReal.one_ne_top (presentMass_le_one law))
  else fallback

/-- The present mass times the conditioned law is the law of the present
values. -/
theorem presentMass_mul_presentConditional (law : PMF (Option β)) (fallback : PMF β) (b : β) :
    presentMass law * presentConditional law fallback b = law (some b) := by
  unfold presentConditional
  split_ifs with present
  · rw [PMF.normalize_apply, mul_comm, mul_assoc]
    change law (some b) * ((presentMass law)⁻¹ * presentMass law) = law (some b)
    rw [ENNReal.inv_mul_cancel present
      (ne_top_of_le_ne_top ENNReal.one_ne_top (presentMass_le_one law)), mul_one]
  · have zero : presentMass law = 0 := not_not.mp present
    rw [zero, zero_mul]
    exact (ENNReal.tsum_eq_zero.mp zero b).symm

/-- The law of an optional pair, at a present pair, through a kernel that pairs
its noise with each state. -/
private theorem bind_pair_apply (prior : PMF β) (kernel : β → PMF (Option γ)) (c : β) (t : γ) :
    (prior.bind fun state => (kernel state).map (Option.map fun noise => (state, noise)))
        (some (c, t)) = prior c * kernel c (some t) := by
  classical
  rw [PMF.bind_apply, tsum_eq_single c]
  · rw [PMF.map_apply, tsum_eq_single (some t)]
    · simp
    · intro other different
      cases other with
      | none => simp
      | some other =>
          have : (c, t) ≠ (c, other) := fun same => different (by
            rw [(Prod.mk.inj same).2])
          simp [this]
  · intro other different
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro noise
    split_ifs with same
    · cases noise with
      | none => cases same
      | some noise =>
          exact (different (Prod.mk.inj (Option.some.inj same)).1.symm).elim
    · rfl

/-- A law of optional values dominated at its present values by a law of
values stays dominated through any map. -/
theorem map_some_apply_le {A : PMF (Option β)} {B : PMF β}
    (dominated : ∀ value, A (some value) ≤ B value) (map : β → γ) (image : γ) :
    (A.map (Option.map map)) (some image) ≤ (B.map map) image := by
  classical
  simp only [PMF.map_apply]
  rw [tsum_eq_tsum_of_ne_zero_bij (fun value : {value : β //
      (if image = map value then A (some value) else 0) ≠ 0} => some value.val)]
  · apply ENNReal.tsum_le_tsum
    intro value
    split_ifs
    · exact dominated value
    · exact le_rfl
  · intro first second same
    exact Subtype.ext (Option.some.inj same)
  · intro option nonzero
    cases option with
    | none => simp at nonzero
    | some value =>
        refine ⟨⟨value, ?_⟩, rfl⟩
        intro zero
        apply nonzero
        dsimp only
        split_ifs with same
        · have equal : image = map value := Option.some.inj same
          simpa [equal] using zero
        · rfl
  · intro value
    simp

/-- Scaling a law dominated by another, after scaling, dominates through every
kernel. -/
theorem mul_bind_apply_le {μ ν : PMF β} {scale : ℝ≥0∞}
    (dominated : ∀ value, scale * μ value ≤ ν value)
    (kernel : β → PMF γ) (image : γ) :
    scale * (μ.bind kernel) image ≤ (ν.bind kernel) image := by
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro value
  rw [← mul_assoc]
  exact mul_le_mul' (dominated value) le_rfl

section Factor

variable (law : PMF α) (alive : α → Prop) [DecidablePred alive]
  (observable : α → β × γ) (prior : PMF β) (kernel : W → PMF (Option γ)) (view : β → W)

/-- **The survivors' joint law, weighted by their mass,** is the surviving
part of the factorized law. -/
theorem filter_joint_mul
    (factor : law.map (fun a => if alive a then some (observable a) else none) =
      prior.bind fun c => (kernel (view c)).map (Option.map fun t => (c, t)))
    (present : ∃ a ∈ {a | alive a}, a ∈ law.support) (c : β) (t : γ) :
    (∑' x, ({a | alive a} : Set α).indicator law x) *
        ((law.filter {a | alive a} present).map observable) (c, t) =
      prior c * kernel (view c) (some t) := by
  classical
  rw [← bind_pair_apply prior (fun c => kernel (view c)) c t, ← factor, PMF.map_apply,
    PMF.map_apply, ← ENNReal.tsum_mul_left]
  congr 1
  funext a
  rw [mul_ite, mul_zero, filter_mass_mul]
  by_cases living : alive a
  · simp [living]
  · simp [living]

/-- **The survivors' state law, weighted by their mass,** is the law of the
state times the kernel's surviving mass at its observation. -/
theorem filter_marginal_mul
    (factor : law.map (fun a => if alive a then some (observable a) else none) =
      prior.bind fun c => (kernel (view c)).map (Option.map fun t => (c, t)))
    (present : ∃ a ∈ {a | alive a}, a ∈ law.support) (c : β) :
    (∑' x, ({a | alive a} : Set α).indicator law x) *
        ((law.filter {a | alive a} present).map fun a => (observable a).1) c =
      prior c * presentMass (kernel (view c)) := by
  classical
  have split : ((law.filter {a | alive a} present).map fun a => (observable a).1) c =
      ∑' t, ((law.filter {a | alive a} present).map observable) (c, t) := by
    rw [show (fun a => (observable a).1) = Prod.fst ∘ observable from rfl, ← PMF.map_comp,
      PMF.map_apply]
    have product := ENNReal.tsum_prod (f := fun (first : β) (second : γ) =>
      if c = first then ((law.filter {a | alive a} present).map observable) (first, second)
        else 0)
    refine product.trans ?_
    rw [tsum_eq_single c]
    · simp
    · intro other different
      simp [Ne.symm different]
  rw [split, ← ENNReal.tsum_mul_left]
  simp only [filter_joint_mul law alive observable prior kernel view factor present]
  rw [ENNReal.tsum_mul_left]
  rfl

/-- **The survivors' state law, weighted by their mass, is dominated** by the
law of the state. -/
theorem filter_marginal_le
    (factor : law.map (fun a => if alive a then some (observable a) else none) =
      prior.bind fun c => (kernel (view c)).map (Option.map fun t => (c, t)))
    (present : ∃ a ∈ {a | alive a}, a ∈ law.support) (c : β) :
    (∑' x, ({a | alive a} : Set α).indicator law x) *
        ((law.filter {a | alive a} present).map fun a => (observable a).1) c ≤ prior c := by
  rw [filter_marginal_mul law alive observable prior kernel view factor present]
  calc prior c * presentMass (kernel (view c)) ≤ prior c * 1 :=
        mul_le_mul' le_rfl (presentMass_le_one _)
    _ = prior c := mul_one _

/-- **Conditioning a factorized survival on survival.** When the surviving
part of a joint law of a state and a noise is the law of a state with the noise
of a kernel of its observation that may report that nothing survives, the
survivors conditioned on survival have, given their state, the noise of the
kernel conditioned on presence. -/
theorem filter_map_factor (fallback : W → PMF γ)
    (factor : law.map (fun a => if alive a then some (observable a) else none) =
      prior.bind fun c => (kernel (view c)).map (Option.map fun t => (c, t)))
    (present : ∃ a ∈ {a | alive a}, a ∈ law.support) :
    (law.filter {a | alive a} present).map observable =
      ((law.filter {a | alive a} present).map fun a => (observable a).1).bind fun c =>
        (presentConditional (kernel (view c)) (fallback (view c))).map fun t => (c, t) := by
  classical
  let mass := ∑' x, ({a | alive a} : Set α).indicator law x
  have massPositive : mass ≠ 0 := by simpa [mass] using present
  have massFinite : mass ≠ ⊤ := law.tsum_coe_indicator_ne_top _
  ext ⟨c, t⟩
  apply (ENNReal.mul_right_inj massPositive massFinite).mp
  rw [filter_joint_mul law alive observable prior kernel view factor present, PMF.bind_apply,
    ← ENNReal.tsum_mul_left, tsum_eq_single c]
  · rw [← mul_assoc, filter_marginal_mul law alive observable prior kernel view factor present,
      PMF.map_apply, tsum_eq_single t]
    · simp only [↓reduceIte]
      rw [mul_assoc, presentMass_mul_presentConditional]
    · intro other different
      have : (c, t) ≠ (c, other) := fun same => different (Prod.mk.inj same).2.symm
      simp [this]
  · intro other different
    have zero : ((presentConditional (kernel (view other)) (fallback (view other))).map
        fun noise => (other, noise)) (c, t) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr]
      intro noise
      split_ifs with same
      · exact (different (Prod.mk.inj same).1.symm).elim
      · rfl
    rw [zero, mul_zero, mul_zero]

end Factor

end GameTheory.Math.Probability
