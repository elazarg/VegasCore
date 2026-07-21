/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNRat.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.Probability

/-!
# Finite-support weights

This file provides `FWeight α`, the finite-support nonnegative-rational
weight layer used by the probabilistic-language part of Vegas.

## Design

`FWeight α` is `α →₀ ℚ≥0` — a `Finsupp` with nonnegative rational weights.
It is not itself a probability or subprobability type: `totalWeight d` may
take any value in `[0, ∞)`. Probability is expressed by a separate
normalization proof.

Three choices distinguish it from Mathlib's `PMF`:

* **Raw weights.** Normalization is tracked as a separately-discharged
  invariant (see `Normalized` and `totalWeight_bind_of_normalized`), so
  intermediate `bind`-trees can be built without per-step normalization proofs.
* **Rational weights.** Equality is decidable and concrete finite weights are
  computationally meaningful, which keeps examples and finite transformations
  inspectable.
* **Decidable carrier.** `[DecidableEq α]` is what makes `Finsupp`
  arithmetic and the `support` Finset usable.

## Layout

* The monadic operations `pure`, `zero`, `bind`, `map`, plus `totalWeight`
  and the data-constructor `ofList`.
* Pointwise formulae (`pure_apply`, `bind_apply`, `map_apply`) and the
  `Supported` predicate used to express "every value with positive weight
  satisfies `P`".
* The monad and functor laws, including commutativity (`bind_comm`), which
  underpins program-level commutation theorems in the Vegas semantics.
* A bridge `toPMF : (d : FWeight α) → d.totalWeight = 1 → PMF α` into
  Mathlib's measure-theoretic `PMF`. The bridge is one-way and is the only
  exit point from `FWeight`.

`pure` and `zero` are computable — they're built directly from the underlying
`Finsupp` record using the `[DecidableEq α]` we carry. `bind`, `map`
and the `toPMF` bridge remain `noncomputable` because they
route through `Finsupp.sum`, which Mathlib marks `noncomputable`. Reasoning
about all of them is fully constructive; `#eval` works on Dirac masses but
not on bind-trees.
-/

namespace Vegas

/-- Finite-support nonnegative-rational weights over a type with decidable
equality. See the file docstring for design rationale. -/
abbrev FWeight (α : Type) [DecidableEq α] := α →₀ ℚ≥0

namespace FWeight

variable {α : Type} {β : Type} [DecidableEq α] [DecidableEq β]

/-! ## Operations -/

/-- The Dirac mass at `x`: weight `1` on `x`, weight `0` elsewhere.

Built directly rather than via `Finsupp.single` (which is `noncomputable`
because it uses `Classical.dec` internally to decide `b = 0`). The
`[DecidableEq α]` on `FWeight α` lets us construct the underlying `Finsupp`
record with computable support and indicator function. -/
def pure (x : α) : FWeight α where
  support := {x}
  toFun y := if y = x then 1 else 0
  mem_support_toFun y := by
    by_cases h : y = x
    · subst h; simp
    · simp [h]

/-- The empty weight; total weight `0`. Acts as the identity for addition and
as the absorbing element for `bind` on the left (`bind_zero_left`). -/
def zero : FWeight α := 0

/-- Monadic continuation: each support point `a` of `d`, weighted by `w`,
contributes the weight `f a` rescaled by `w`. -/
noncomputable def bind (d : FWeight α) (f : α → FWeight β) : FWeight β :=
  d.sum fun a w => (f a).mapRange (w * ·) (mul_zero w)

/-- Pushforward of `d` along `g`. If `g` is not injective, the weights of
collided keys add. -/
noncomputable def map (g : α → β) (d : FWeight α) : FWeight β :=
  d.mapDomain g

/-- Total mass of `d` — the sum of weights over the support. Equals `1`
exactly for normalized weights. -/
def totalWeight (d : FWeight α) : ℚ≥0 := d.sum (fun _ w => w)

/-- A finite weight is normalized when its total mass is exactly `1`. This is
the invariant required before crossing from `FWeight` into `PMF`. -/
def Normalized (d : FWeight α) : Prop := d.totalWeight = 1

/-! ## Constructors from data -/

/-- Sum of all weights for key `a` in an association list. Defined
recursively so that `ofList` can be built without classical choice on the
list structure. -/
def ofListWeight (a : α) : List (α × ℚ≥0) → ℚ≥0
  | [] => 0
  | entry :: rest => (if entry.1 = a then entry.2 else 0) + ofListWeight a rest

/-- Build an `FWeight` from an explicit list of `(value, weight)` entries.
Duplicate keys add; entries with weight `0` (or whose weights cancel to `0`
through duplication) are filtered from the support. This is the only data
constructor of `FWeight`; every other weight arises from `pure`,
`bind`, `map`, or a user-supplied kernel. -/
def ofList (entries : List (α × ℚ≥0)) : FWeight α where
  support := (entries.map Prod.fst).toFinset.filter (fun a => ofListWeight a entries ≠ 0)
  toFun a := ofListWeight a entries
  mem_support_toFun a := by
    rw [Finset.mem_filter]
    constructor
    · intro h
      exact h.2
    · intro hne
      constructor
      · simp only [List.mem_toFinset, List.mem_map]
        induction entries with
        | nil => simp [ofListWeight] at hne
        | cons hd tl ih =>
            simp only [ofListWeight] at hne
            by_cases h : hd.1 = a
            · exact ⟨hd, by simp, h⟩
            · have htail : ofListWeight a tl ≠ 0 := by
                intro hzero
                apply hne
                simp [h, hzero]
              rcases ih htail with ⟨entry, hmem, heq⟩
              exact ⟨entry, List.mem_cons_of_mem hd hmem, heq⟩
      · exact hne

/-! ## Pointwise formulae and support -/

@[simp] theorem pure_apply (x y : α) : FWeight.pure x y = if x = y then 1 else 0 := by
  change (if y = x then 1 else 0 : ℚ≥0) = _
  by_cases h : x = y
  · subst h; simp
  · have : y ≠ x := fun e => h e.symm
    simp [h, this]

/-- Pointwise unfolding of `bind` to a finite sum over the support of `d`.
Not a `simp` lemma: applied eagerly it would expand bind-heavy terms. Use
explicitly when a pointwise formula is needed, for example in adequacy or
support-correctness proofs. -/
theorem bind_apply (d : FWeight α) (f : α → FWeight β) (b : β) :
    (d.bind f) b = d.support.sum (fun a => d a * (f a) b) := by
  simp only [bind, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.mapRange_apply]

/-- Pointwise unfolding of `map` to a finite sum over the support of `d`.
The conditional handles the case where `g` collides keys; `map_apply_injective`
and `map_apply_of_forall_ne` are the two clean specializations that avoid it. -/
theorem map_apply (g : α → β) (d : FWeight α) (b : β) :
    (d.map g) b = d.support.sum (fun a => if g a = b then d a else 0) := by
  simp [map, Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- "`P` holds at every value with positive weight". The standard idiom for
expressing semantic side conditions on a finite weight — for example, the
fair-play requirement that every committed action satisfies its guard. -/
def Supported (d : FWeight α) (P : α → Prop) : Prop := ∀ a ∈ d.support, P a

@[simp] theorem support_pure (x : α) : (FWeight.pure x).support = {x} := rfl

@[simp] theorem totalWeight_pure (x : α) : (FWeight.pure x).totalWeight = 1 := by
  simp [totalWeight, Finsupp.sum, support_pure, pure_apply]

@[simp] theorem support_zero : (FWeight.zero : FWeight α).support = ∅ :=
  Finsupp.support_zero

@[simp] theorem Supported_pure {P : α → Prop} (x : α) :
    (FWeight.pure x).Supported P ↔ P x := by
  simp [Supported]

theorem pure_bind (x : α) (f : α → FWeight β) : (FWeight.pure x).bind f = f x := by
  ext b
  rw [bind_apply]
  simp [support_pure, pure_apply]

theorem bind_pure (d : FWeight α) : d.bind FWeight.pure = d := by
  ext b
  rw [bind_apply]
  simp only [pure_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' d.support b (fun a => d a)]
  by_cases h : b ∈ d.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h]

theorem bind_zero_left (f : α → FWeight β) :
    (FWeight.zero : FWeight α).bind f = FWeight.zero := by
  simp [bind, FWeight.zero, Finsupp.sum_zero_index]

@[simp] theorem ofList_nil : (FWeight.ofList (α := α) []) = FWeight.zero := by
  ext a
  simp [ofList, ofListWeight, FWeight.zero]

theorem ofList_cons (a : α) (w : ℚ≥0) (rest : List (α × ℚ≥0)) :
    FWeight.ofList ((a, w) :: rest) = Finsupp.single a w + FWeight.ofList rest := by
  ext x
  simp [ofList, ofListWeight, Finsupp.single_apply]

/-- Support characterization of `bind`: `b` is reachable through `d.bind f`
iff some `a` in `d`'s support carries `b` in `f a`'s support. The basis for
"reachable iff in support" theorems at the program level. -/
theorem mem_support_bind {d : FWeight α} {f : α → FWeight β} {b : β} :
    b ∈ (d.bind f).support ↔ ∃ a ∈ d.support, b ∈ (f a).support := by
  rw [Finsupp.mem_support_iff, bind_apply]
  constructor
  · intro h
    by_contra hall
    push Not at hall
    apply h
    apply Finset.sum_eq_zero
    intro a ha
    have hfab : (f a) b = 0 := by
      by_contra hne
      exact hall a ha (Finsupp.mem_support_iff.mpr hne)
    rw [hfab, mul_zero]
  · rintro ⟨a, ha, hb⟩ heq
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha)
      (Finsupp.mem_support_iff.mp hb)
      (Finset.sum_eq_zero_iff.mp heq a ha)

/-- Support characterization of `map`: a target has positive mass exactly when
some positive-mass source maps to it. -/
theorem mem_support_map {d : FWeight α} {g : α → β} {b : β} :
    b ∈ (d.map g).support ↔ ∃ a ∈ d.support, g a = b := by
  rw [Finsupp.mem_support_iff, map_apply]
  constructor
  · intro h
    by_contra hall
    push Not at hall
    apply h
    apply Finset.sum_eq_zero
    intro a ha
    have hne : g a ≠ b := fun hg => hall a ha hg
    simp [hne]
  · rintro ⟨a, ha, hg⟩ hzero
    have hterm := Finset.sum_eq_zero_iff.mp hzero a ha
    rw [if_pos hg] at hterm
    exact Finsupp.mem_support_iff.mp ha hterm

@[simp] theorem mem_support_pure {a b : α} :
    b ∈ (FWeight.pure a).support ↔ b = a := by
  rw [support_pure, Finset.mem_singleton]

/-! ## Algebraic laws and total-weight propagation -/

/-- Total mass of a `bind` is the weighted sum of the branches' total
masses. The general identity from which the normalized version
(`totalWeight_bind_of_normalized`) is derived. -/
theorem totalWeight_bind (d : FWeight α) (f : α → FWeight β) :
    (d.bind f).totalWeight = d.support.sum (fun a => d a * (f a).totalWeight) := by
  unfold totalWeight bind
  rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  have hmr : ∀ (a : α) (w : ℚ≥0),
      (Finsupp.mapRange (w * ·) (mul_zero w) (f a)).sum (fun _ x => x) =
        (f a).sum (fun _ b => w * b) := fun _ _ =>
      Finsupp.sum_mapRange_index (fun _ => rfl)
  simp_rw [hmr]
  simp only [Finsupp.sum, Finset.mul_sum]

/-- Normalization propagates through `bind`: a normalized head and uniformly
normalized branches give a normalized result. The single load-bearing lemma
behind every `outcomeDist_totalWeight_eq_one`-style induction in the Vegas
semantics. -/
theorem totalWeight_bind_of_normalized {d : FWeight α} {f : α → FWeight β}
    (hd : d.totalWeight = 1) (hf : ∀ a ∈ d.support, (f a).totalWeight = 1) :
    (d.bind f).totalWeight = 1 := by
  rw [totalWeight_bind]
  have hs : d.support.sum (fun a => d a * (f a).totalWeight) = d.support.sum (fun a => d a) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hf a ha, mul_one]
  rw [hs]
  exact hd

/-- Pushforward through an injective `g` is read pointwise: no collisions, so
`(d.map g) (g a) = d a`. Avoids the conditional in `map_apply`. -/
theorem map_apply_injective (g : α → β) (d : FWeight α) (a : α)
    (hinj : Function.Injective g) :
    (d.map g) (g a) = d a := by
  simpa [map] using Finsupp.mapDomain_apply (f := g) hinj d a

/-- A point `b` outside the image of `g` on the support of `d` carries weight
`0` in the pushforward. The companion to `map_apply_injective` for the
"`b` is unreachable" case. -/
theorem map_apply_of_forall_ne (g : α → β) (d : FWeight α) (b : β)
    (h : ∀ a ∈ d.support, g a ≠ b) :
    (d.map g) b = 0 := by
  rw [map_apply]
  apply Finset.sum_eq_zero
  intro a ha
  simp [h a ha]

theorem map_pure (g : α → β) (a : α) :
    (FWeight.pure a).map g = FWeight.pure (g a) := by
  ext b
  rw [map_apply]
  simp only [support_pure, Finset.sum_singleton, pure_apply]
  by_cases h : g a = b
  · simp [h]
  · simp [h]

theorem map_map {γ : Type} [DecidableEq γ] (f : α → β) (g : β → γ) (d : FWeight α) :
    (d.map f).map g = d.map (g ∘ f) := by
  simpa [map] using (Finsupp.mapDomain_comp (v := d) (f := f) (g := g)).symm

theorem bind_map (d : FWeight α) (f : α → FWeight β) {γ : Type} [DecidableEq γ]
    (g : β → γ) :
    (d.bind f).map g = d.bind (fun a => (f a).map g) := by
  simp only [bind, map]
  change (Finsupp.mapDomain.addMonoidHom g)
      (d.sum fun a w => Finsupp.mapRange (fun x => w * x) (mul_zero w) (f a)) =
    d.sum fun a w => Finsupp.mapRange (fun x => w * x) (mul_zero w) (Finsupp.mapDomain g (f a))
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro a _
  exact Finsupp.mapDomain_mapRange
    (f := g) (v := f a) (g := fun x : ℚ≥0 => d a * x)
    (h0 := mul_zero (d a)) (hadd := by intro x y; exact mul_add (d a) x y)

/-- Independent `bind`s commute: the order in which two independent random
choices are made does not affect the joint distribution. The algebraic
substrate for program-level commutation results — for example, two adjacent
commits with independent strategies produce the same outcome distribution
regardless of order. -/
theorem bind_comm {γ : Type} [DecidableEq γ]
    (d₁ : FWeight α) (d₂ : FWeight β) (f : α → β → FWeight γ) :
    d₁.bind (fun a => d₂.bind (fun b => f a b)) =
      d₂.bind (fun b => d₁.bind (fun a => f a b)) := by
  ext c
  simp only [bind_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_left_comm (d₁ a) (d₂ b) ((f a b) c)

theorem totalWeight_map (d : FWeight α) (g : α → β) :
    FWeight.totalWeight (FWeight.map g d) = FWeight.totalWeight d := by
  simp only [FWeight.map, FWeight.totalWeight]
  let h : β → ℚ≥0 →+ ℚ≥0 := fun _ => AddMonoidHom.id ℚ≥0
  simpa [h] using
    (Finsupp.sum_mapDomain_index_addMonoidHom (f := g) (s := d) (h := h))

end FWeight

/-! ## Cast `ℚ≥0 → ℝ≥0`

The bridge to `PMF` produces `ENNReal` weights. Mathlib does not ship a
direct ring map `ℚ≥0 → ENNReal`, so we go via `NNReal`. The lemmas below
are the targeted rewrite rules used inside the bridge — none are `@[simp]`. -/

/-- Canonical embedding `ℚ≥0 → ℝ≥0`. -/
noncomputable def nnratToNNReal (q : ℚ≥0) : NNReal :=
  ⟨((q : ℚ) : ℝ), by exact_mod_cast q.coe_nonneg⟩

theorem nnratToNNReal_one : nnratToNNReal 1 = 1 := by
  refine NNReal.coe_injective ?_
  change (((1 : ℚ≥0) : ℚ) : ℝ) = 1
  norm_num

theorem nnratToNNReal_zero : nnratToNNReal 0 = 0 := by
  refine NNReal.coe_injective ?_
  change (((0 : ℚ≥0) : ℚ) : ℝ) = 0
  norm_num

theorem nnratToNNReal_eq_zero {q : ℚ≥0} :
    nnratToNNReal q = 0 ↔ q = 0 := by
  constructor
  · intro h
    have hcoe := congrArg (fun value : NNReal => (value : ℝ)) h
    change ((q : ℚ) : ℝ) = 0 at hcoe
    exact_mod_cast hcoe
  · intro h
    subst h
    exact nnratToNNReal_zero

theorem nnratToNNReal_add (a b : ℚ≥0) :
    nnratToNNReal (a + b) = nnratToNNReal a + nnratToNNReal b := by
  refine NNReal.coe_injective ?_
  change ((((a + b : ℚ≥0) : ℚ) : ℝ) = (((a : ℚ≥0) : ℚ) : ℝ) + (((b : ℚ≥0) : ℚ) : ℝ))
  rw [NNRat.coe_add, Rat.cast_add]

theorem nnratToNNReal_mul (a b : ℚ≥0) :
    nnratToNNReal (a * b) = nnratToNNReal a * nnratToNNReal b := by
  refine NNReal.coe_injective ?_
  change ((((a * b : ℚ≥0) : ℚ) : ℝ) = (((a : ℚ≥0) : ℚ) : ℝ) * (((b : ℚ≥0) : ℚ) : ℝ))
  rw [NNRat.coe_mul, Rat.cast_mul]

theorem nnratToNNReal_coe_real (q : ℚ≥0) :
    ((nnratToNNReal q : NNReal) : ℝ) = (q : ℝ) := by
  rfl

theorem nnratToNNReal_finset_sum {γ : Type} (s : Finset γ) (f : γ → ℚ≥0) :
    nnratToNNReal (s.sum f) = s.sum (fun a => nnratToNNReal (f a)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [nnratToNNReal_zero]
  · intro a s ha hs
    simp [Finset.sum_insert, ha, nnratToNNReal_add, hs]

namespace FWeight

/-! ## Bridge to `PMF`

`toPMF` casts a normalized `FWeight` into a Mathlib `PMF`. The bridge is a
monad homomorphism (`toPMF_pure`, `toPMF_bind`, `toPMF_map`), and
`expect_toPMF_eq_sum` reduces `PMF`-expectations to finite rational sums
— the basis for computable expected utility in the strategic semantics.
The bridge is one-way: `PMF → FWeight` does not exist in general (a `PMF`
may carry irrational or infinite-support weights). -/

/-- Convert a normalized finite-support weight into a `PMF`. -/
noncomputable def toPMF {γ : Type} [DecidableEq γ]
    (d : FWeight γ) (h : d.totalWeight = 1) : PMF γ :=
  PMF.ofFinset
    (fun a => (nnratToNNReal (d a) : ENNReal))
    d.support
    (by
      have hsum : d.support.sum (fun a => d a) = 1 := by
        simpa [FWeight.totalWeight, Finsupp.sum] using h
      calc
        d.support.sum (fun a => ((nnratToNNReal (d a) : NNReal) : ENNReal))
            = ((d.support.sum fun a => nnratToNNReal (d a) : NNReal) : ENNReal) := by
                rw [← ENNReal.ofNNReal_finsetSum]
        _ = (nnratToNNReal (d.support.sum fun a => d a) : ENNReal) := by
              rw [nnratToNNReal_finset_sum]
        _ = 1 := by simp [hsum, nnratToNNReal_one])
    (by
      intro a ha
      have hz : d a = 0 := by
        simpa [Finsupp.mem_support_iff] using ha
      simp [hz, nnratToNNReal_zero])

/-- `toPMF` applied at a point equals the cast of the original weight. -/
theorem toPMF_apply {γ : Type} [DecidableEq γ]
    (d : FWeight γ) (h : d.totalWeight = 1) (a : γ) :
    (d.toPMF h) a = (nnratToNNReal (d a) : ENNReal) := by
  simp [FWeight.toPMF, PMF.ofFinset_apply]

/-- `FWeight.toPMF` preserves and reflects finite support. -/
theorem mem_support_toPMF {γ : Type} [DecidableEq γ]
    (d : FWeight γ) (h : d.totalWeight = 1) (a : γ) :
    a ∈ (d.toPMF h).support ↔ a ∈ d.support := by
  rw [PMF.mem_support_iff, Finsupp.mem_support_iff, toPMF_apply]
  constructor
  · intro hpmf hzero
    exact hpmf (by simp [hzero, nnratToNNReal_zero])
  · intro hweight
    simpa [nnratToNNReal_eq_zero] using hweight

/-- `toPMF` converts `FWeight.pure` to `PMF.pure`. -/
theorem toPMF_pure [DecidableEq α] (a : α) :
    (FWeight.pure a).toPMF (FWeight.totalWeight_pure a) = PMF.pure a := by
  ext b
  rw [toPMF_apply]
  simp only [PMF.pure_apply, pure_apply]
  by_cases h : a = b
  · subst h; simp [nnratToNNReal_one]
  · simp [h, nnratToNNReal_zero, Ne.symm h]

/-- `toPMF` converts `FWeight.map` to `PMF.map`. -/
theorem toPMF_map [DecidableEq α] [DecidableEq β]
    (d : FWeight α) (g : α → β) (h : d.totalWeight = 1)
    (hmap : (d.map g).totalWeight = 1) :
    (d.map g).toPMF hmap = (d.toPMF h).map g := by
  ext b
  rw [toPMF_apply]
  simp only [PMF.map_apply, toPMF_apply]
  rw [FWeight.map_apply]
  rw [tsum_eq_sum (s := d.support) (fun a ha => by
    have hz : d a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    simp [hz, nnratToNNReal_zero])]
  have hlhs :
      ((nnratToNNReal (∑ a ∈ d.support, if g a = b then d a else 0) : NNReal) : ENNReal) =
        ∑ a ∈ d.support, ((nnratToNNReal (if g a = b then d a else 0) : NNReal) : ENNReal) := by
    rw [nnratToNNReal_finset_sum, ENNReal.ofNNReal_finsetSum]
  rw [hlhs]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hgab : g a = b
  · simp [hgab]
  · simp [hgab, Ne.symm hgab, nnratToNNReal_zero]

/-- Pointwise `toPMF` of `FWeight.bind`. -/
theorem toPMF_bind_apply [DecidableEq α] [DecidableEq β]
    (d : FWeight α) (f : α → FWeight β)
    (hbind : (d.bind f).totalWeight = 1) (b : β) :
    ((d.bind f).toPMF hbind) b =
      d.support.sum (fun a =>
        (nnratToNNReal (d a) : ENNReal) * (nnratToNNReal ((f a) b) : ENNReal)) := by
  rw [toPMF_apply, bind_apply]
  rw [show ((nnratToNNReal (d.support.sum fun a => d a * (f a) b) : NNReal) : ENNReal) =
      d.support.sum (fun a => ((nnratToNNReal (d a * (f a) b) : NNReal) : ENNReal)) from by
    rw [nnratToNNReal_finset_sum, ENNReal.ofNNReal_finsetSum]]
  apply Finset.sum_congr rfl
  intro a _
  rw [nnratToNNReal_mul, ENNReal.coe_mul]

/-- `toPMF` commutes with `bind` when the branches are normalized. -/
theorem toPMF_bind [DecidableEq α] [DecidableEq β]
    (d : FWeight α) (f : α → FWeight β)
    (hd : d.totalWeight = 1)
    (hf : ∀ a, FWeight.totalWeight (f a) = 1)
    (hbind : (FWeight.bind d f).totalWeight = 1) :
    (FWeight.bind d f).toPMF hbind =
      (d.toPMF hd).bind (fun a => (f a).toPMF (hf a)) := by
  ext b
  rw [toPMF_bind_apply]
  simp only [PMF.bind_apply, toPMF_apply]
  rw [tsum_eq_sum (s := d.support) (fun a ha => by
    have hz : d a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    simp [hz, nnratToNNReal_zero])]

/-- Expectation under `FWeight.toPMF` reduces to a finite sum over support. -/
theorem expect_toPMF_eq_sum {γ : Type} [DecidableEq γ]
    (d : FWeight γ) (h : d.totalWeight = 1) (f : γ → ℝ) :
    Math.Probability.expect (d.toPMF h) f =
      d.support.sum (fun a => ((nnratToNNReal (d a) : NNReal) : ℝ) * f a) := by
  unfold Math.Probability.expect
  rw [tsum_eq_sum (s := d.support)]
  · refine Finset.sum_congr rfl ?_
    intro a ha
    simp [FWeight.toPMF]
  · intro a ha
    have hz : d a = 0 := by
      simpa [Finsupp.mem_support_iff] using ha
    simp [FWeight.toPMF, hz, nnratToNNReal_zero]

end FWeight

end Vegas
