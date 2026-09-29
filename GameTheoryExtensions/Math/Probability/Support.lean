/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Support

/-! # Support-local algebra of probability mass functions

Pushforwards and binds are determined by their behavior on the support of the
source law. These laws complement the upstream support lemmas.
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {α β γ δ : Type*}

open Classical in
/-- The real mass of a point law. -/
theorem toReal_pure_apply (b a : α) : ((PMF.pure b) a).toReal = if a = b then 1 else 0 := by
  rw [PMF.pure_apply]
  split_ifs <;> simp

/-- The real atom masses of a law on a finite carrier sum to one. -/
theorem pmf_sum_toReal_eq_one [Fintype α] (μ : PMF α) : ∑ a, (μ a).toReal = 1 := by
  have total := μ.tsum_coe
  rw [tsum_fintype] at total
  rw [← ENNReal.toReal_sum fun a _ => μ.apply_ne_top a, total, ENNReal.toReal_one]

/-- A constant pushforward is the point law. Mathlib states this for the
constant-function combinator, which `simp` does not match against a literal
`fun _ => b`. -/
theorem pmf_map_fun_const (μ : PMF α) (b : β) : μ.map (fun _ => b) = PMF.pure b :=
  PMF.map_const μ b

/-- Binding into point laws is a pushforward. Mathlib states this for the
composite `PMF.pure ∘ f`, which `simp` does not match against
`fun a => PMF.pure (f a)`. -/
theorem pmf_bind_pure_eq_map (μ : PMF α) (f : α → β) :
    (μ.bind fun a => PMF.pure (f a)) = μ.map f :=
  PMF.bind_pure_comp f μ

/-- A point has positive real mass exactly when it is supported. -/
theorem pmf_toReal_pos_iff {μ : PMF α} {a : α} : 0 < (μ a).toReal ↔ a ∈ μ.support := by
  rw [ENNReal.toReal_pos_iff, PMF.mem_support_iff, pos_iff_ne_zero]
  exact and_iff_left (μ.apply_lt_top a)

/-- An atom has zero real mass exactly when it lies outside the support. -/
theorem pmf_toReal_eq_zero_iff {μ : PMF α} {a : α} : (μ a).toReal = 0 ↔ a ∉ μ.support := by
  rw [ENNReal.toReal_eq_zero_iff, or_iff_left (μ.apply_ne_top a), PMF.apply_eq_zero_iff]

/-- Laws with the same real atom masses are equal. -/
theorem pmf_ext_toReal {μ ν : PMF α} (same : ∀ a, (μ a).toReal = (ν a).toReal) : μ = ν :=
  PMF.ext fun a => (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top a) (ν.apply_ne_top a)).mp
    (same a)

/-- Conditioning on an event rescales the mass of its intersection with any
other event by the event's own mass. -/
theorem pmf_toOuterMeasure_filter_apply (p : PMF α) (s t : Set α)
    (h : ∃ a ∈ s, a ∈ p.support) :
    (p.filter s h).toOuterMeasure t = p.toOuterMeasure (t ∩ s) / p.toOuterMeasure s := by
  simp only [PMF.toOuterMeasure_apply, div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  by_cases inT : a ∈ t <;> by_cases inS : a ∈ s <;>
    simp [Set.indicator, inT, inS, PMF.filter_apply]

/-- When only one supported branch can produce an outcome, the outcome's mass
is that branch's mass times its conditional mass. -/
theorem bind_apply_of_unique_branch (law : PMF α) (branch : α → PMF β)
    (outcome : β) (selected : α)
    (unique : ∀ value ∈ law.support, outcome ∈ (branch value).support → value = selected) :
    (law.bind branch) outcome = law selected * branch selected outcome := by
  rw [PMF.bind_apply, tsum_eq_single selected]
  intro value different
  by_cases supported : value ∈ law.support
  · have absent : outcome ∉ (branch value).support := fun present =>
      different (unique value supported present)
    rw [(PMF.apply_eq_zero_iff _ _).mpr absent, mul_zero]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul]

/-- Pushforwards agree when their functions agree everywhere the source law
can actually draw. -/
theorem map_congr_on_support (μ : PMF α) {f g : α → β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.map f = μ.map g := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact bind_congr_on_support μ fun a ha => by rw [Function.comp_apply, h a ha]; rfl

/-- Equal summary laws may be composed with continuations agreeing on every
pair of supported inputs with the same summary. -/
theorem bind_eq_of_map_eq (μ : PMF α) (ν : PMF β)
    (f : α → γ) (g : β → γ) (hmap : μ.map f = ν.map g)
    (F : α → PMF δ) (H : β → PMF δ)
    (hagree : ∀ a ∈ μ.support, ∀ b ∈ ν.support,
      f a = g b → F a = H b) :
    μ.bind F = ν.bind H := by
  classical
  let representative (c : γ) : β :=
    if h : ∃ b ∈ ν.support, g b = c then h.choose else ν.support_nonempty.choose
  let kernel (c : γ) := H (representative c)
  have hrep (c : γ) (hc : c ∈ (ν.map g).support) :
      representative c ∈ ν.support ∧ g (representative c) = c := by
    have hex : ∃ b ∈ ν.support, g b = c := by simpa using hc
    simp only [representative, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hfirst (a : α) (ha : a ∈ μ.support) : F a = kernel (f a) := by
    have hc : f a ∈ (ν.map g).support := by
      rw [← hmap, PMF.support_map]
      exact ⟨a, ha, rfl⟩
    exact hagree a ha _ (hrep _ hc).1 (hrep _ hc).2.symm
  have hsecond (b : β) (hb : b ∈ ν.support) : H b = kernel (g b) := by
    have hc : g b ∈ (μ.map f).support := by
      rw [hmap, PMF.support_map]
      exact ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hab⟩ := (show g b ∈ f '' μ.support by simpa using hc)
    rw [← hagree a ha b hb hab, ← hab]
    exact hfirst a ha
  calc
    μ.bind F = (μ.map f).bind kernel := by
      rw [PMF.bind_map]
      exact bind_congr_on_support μ hfirst
    _ = (ν.map g).bind kernel := congrArg (fun law => law.bind kernel) hmap
    _ = ν.bind H := by
      rw [PMF.bind_map]
      exact bind_congr_on_support ν fun b hb => (hsecond b hb).symm

/-- A finitely supported law can give every point positive probability only on
a finite carrier. A finite time horizon alone does not provide this premise. -/
theorem FullSupport.finite {law : PMF α} (finiteSupport : law.support.Finite)
    (full : FullSupport law) : Finite α :=
  Set.finite_univ_iff.mp (finiteSupport.subset fun value _ => full value)

/-- Support-dependent binds transport across equality of their source laws
when corresponding branches agree. -/
theorem bindOnSupport_congr_measure {μ ν : PMF α} (same : μ = ν)
    (f : ∀ a ∈ μ.support, PMF β) (g : ∀ a ∈ ν.support, PMF β)
    (agree : ∀ a ha hb, f a ha = g a hb) :
    μ.bindOnSupport f = ν.bindOnSupport g := by
  subst ν
  exact bindOnSupport_congr μ fun a ha => agree a ha ha

/-- A support-dependent bind after an ordinary bind reassociates, with the
intermediate support witness threaded through the inner continuation. -/
theorem bind_bindOnSupport_assoc {γ : Type*} (law : PMF α) (first : α → PMF β)
    (next : ∀ value ∈ (law.bind first).support, PMF γ) :
    (law.bind first).bindOnSupport next =
      law.bindOnSupport fun value valueMem =>
        (first value).bindOnSupport fun result resultMem =>
          next result (by
            rw [PMF.support_bind]
            exact Set.mem_iUnion_of_mem value
              (Set.mem_iUnion_of_mem valueMem resultMem)) := by
  let dependentFirst : ∀ value ∈ law.support, PMF β := fun value _ => first value
  have sourceEq : law.bindOnSupport dependentFirst = law.bind first :=
    PMF.bindOnSupport_eq_bind law first
  calc
    (law.bind first).bindOnSupport next =
        (law.bindOnSupport dependentFirst).bindOnSupport
          (fun value valueMem => next value (by rwa [sourceEq] at valueMem)) := by
      apply bindOnSupport_congr_measure sourceEq.symm
      intro value _ _
      congr
    _ = _ := PMF.bindOnSupport_bindOnSupport law dependentFirst _

/-- A support-dependent continuation after a pushforward can instead be
evaluated at each original draw. The pushforward need not be injective. -/
theorem bindOnSupport_map {γ : Type*} (law : PMF α) (f : α → β)
    (next : ∀ value ∈ (law.map f).support, PMF γ) :
    (law.map f).bindOnSupport next = law.bindOnSupport fun value supported =>
      next (f value) (by rw [PMF.support_map]; exact ⟨value, supported, rfl⟩) := by
  classical
  obtain ⟨someValue, someSupported⟩ := (law.map f).support_nonempty
  let total : β → PMF γ := fun value =>
    if supported : value ∈ (law.map f).support then next value supported
    else next someValue someSupported
  have agrees : ∀ value (supported : value ∈ (law.map f).support),
      next value supported = total value := by
    intro value supported
    simp only [total, supported, ↓reduceDIte]
  rw [bindOnSupport_eq_bind_of_eq_on_support _ agrees, PMF.bind_map]
  symm
  apply bindOnSupport_eq_bind_of_eq_on_support
  intro value supported
  exact agrees (f value) (by rw [PMF.support_map]; exact ⟨value, supported, rfl⟩)

/-- Finitely many finitely supported branches from a finitely supported law
give a finitely supported mixture. -/
theorem bind_support_finite {p : PMF α} {f : α → PMF β} (finite : p.support.Finite)
    (branches : ∀ a ∈ p.support, (f a).support.Finite) : (p.bind f).support.Finite := by
  rw [PMF.support_bind]
  exact finite.biUnion branches

/-- Tagging each branch's draw with its branch makes a tagged atom's mass the
product of the branch mass and the draw's mass within that branch. -/
theorem bind_map_tag_apply (prior : PMF α) (branch : α → PMF β) (value : β) (index : α) :
    (prior.bind fun selected => (branch selected).map fun result => (result, selected))
      (value, index) = prior index * branch index value := by
  rw [PMF.bind_apply, tsum_eq_single index,
    pmf_map_apply_of_injective _ (fun _ _ same => (Prod.mk.inj same).1)]
  intro selected different
  rw [(PMF.apply_eq_zero_iff ((branch selected).map fun result => (result, selected)) _).mpr,
    mul_zero]
  intro member
  obtain ⟨result, _, same⟩ := PMF.support_map .. ▸ member
  exact different (congrArg Prod.snd same)

/-- Retype a law whose entire support satisfies a predicate. This does not
condition or renormalize the law. -/
def pmfToSubtype (law : PMF α) {P : α → Prop}
    (supported : ∀ value ∈ law.support, P value) : PMF {value // P value} :=
  law.bindOnSupport fun value member => PMF.pure ⟨value, supported value member⟩

@[simp] theorem map_val_pmfToSubtype (law : PMF α) {P : α → Prop}
    (supported : ∀ value ∈ law.support, P value) :
    (pmfToSubtype law supported).map Subtype.val = law := by
  rw [pmfToSubtype, map_bindOnSupport,
    bindOnSupport_eq_bind_of_eq_on_support _ (g := PMF.pure) fun _ _ => PMF.pure_map _ _,
    PMF.bind_pure]

theorem map_pmfToSubtype (law : PMF α) {P : α → Prop}
    (supported : ∀ value ∈ law.support, P value) (f : α → β) :
    (pmfToSubtype law supported).map (fun value => f value.1) = law.map f := by
  change (pmfToSubtype law supported).map (f ∘ Subtype.val) = law.map f
  rw [← PMF.map_comp, map_val_pmfToSubtype]

/-- Iterating a kernel after an initial bind is the bind of the iterates. -/
theorem iterate_bind (kernel : β → PMF β) (count : Nat) (law : PMF α)
    (start : α → PMF β) :
    (fun distribution => distribution.bind kernel)^[count] (law.bind start) =
      law.bind (fun value => (fun distribution => distribution.bind kernel)^[count]
        (start value)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [Function.iterate_succ_apply', ih, PMF.bind_bind]

/-- Transporting a law along a type equality maps it by the cast. -/
theorem cast_eq_map_cast {A B : Type _} (same : A = B) (law : PMF A) :
    cast (congrArg PMF same) law = law.map (cast same) := by
  cases same
  exact (PMF.map_id law).symm

/-- A law whose transport is another law is that law mapped back by the cast. -/
theorem eq_map_cast_of_cast_eq {A B : Type _} (same : A = B) (law : PMF A)
    (transported : PMF B) (equal : cast (congrArg PMF same) law = transported) :
    law = transported.map (cast same.symm) := by
  cases same
  cases equal
  exact (PMF.map_id law).symm

end GameTheory.Math.Probability
