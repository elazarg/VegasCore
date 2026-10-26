/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! # Observable spaces closed under labelled operators

The orbit span constructs the least closed space containing the selected
observables. A supplied finite spanning family is a sound certificate without
being minimal or independent. Search for that family need not be trusted.
-/

noncomputable section

namespace GameTheory.Math.InvariantObservables

variable {K V Label Seed Index : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Apply the labelled continuation operators in chronological order. -/
def word (operator : Label → V →ₗ[K] V) : List Label → V →ₗ[K] V
  | [] => LinearMap.id
  | label :: rest => (operator label).comp (word operator rest)

@[simp] theorem word_nil (operator : Label → V →ₗ[K] V) (value : V) :
    word operator [] value = value := rfl

@[simp] theorem word_cons (operator : Label → V →ₗ[K] V)
    (label : Label) (rest : List Label) (value : V) :
    word operator (label :: rest) value = operator label (word operator rest value) := rfl

/-- The space produced by closing all selected observables under every label. -/
def orbitSpan (operator : Label → V →ₗ[K] V) (seed : Seed → V) : Submodule K V :=
  Submodule.span K (Set.range fun pair : List Label × Seed => word operator pair.1 (seed pair.2))

theorem seed_mem_orbitSpan (operator : Label → V →ₗ[K] V) (seed : Seed → V) (index : Seed) :
    seed index ∈ orbitSpan operator seed :=
  Submodule.subset_span ⟨([], index), rfl⟩

theorem operator_mem_orbitSpan (operator : Label → V →ₗ[K] V) (seed : Seed → V)
    (label : Label) {value : V} (member : value ∈ orbitSpan operator seed) :
    operator label value ∈ orbitSpan operator seed := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ member
  · rintro _ ⟨⟨rest, index⟩, rfl⟩
    exact Submodule.subset_span ⟨(label :: rest, index), rfl⟩
  · simp
  · intro left right _ _ leftMember rightMember
    simpa using (orbitSpan operator seed).add_mem leftMember rightMember
  · intro scalar value _ valueMember
    simpa using (orbitSpan operator seed).smul_mem scalar valueMember

/-- Any supplied invariant space containing the seeds contains their orbit. -/
theorem word_mem (operator : Label → V →ₗ[K] V) (space : Submodule K V)
    (closed : ∀ label value, value ∈ space → operator label value ∈ space)
    {value : V} (member : value ∈ space) (labels : List Label) :
    word operator labels value ∈ space := by
  induction labels with
  | nil => exact member
  | cons label rest ih => exact closed label _ ih

theorem orbitSpan_le (operator : Label → V →ₗ[K] V) (seed : Seed → V)
    (space : Submodule K V)
    (contains : ∀ index, seed index ∈ space)
    (closed : ∀ label value, value ∈ space → operator label value ∈ space) :
    orbitSpan operator seed ≤ space := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨labels, index⟩, rfl⟩
  exact word_mem operator space closed (contains index) labels

/-- Checking an operator on the supplied columns suffices for its whole span. -/
theorem map_mem_span (operator : V →ₗ[K] V) (basis : Index → V)
    (closed : ∀ index, operator (basis index) ∈ Submodule.span K (Set.range basis))
    {value : V} (member : value ∈ Submodule.span K (Set.range basis)) :
    operator value ∈ Submodule.span K (Set.range basis) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ member
  · rintro _ ⟨index, rfl⟩; exact closed index
  · simp
  · intro left right _ _ leftMember rightMember
    simpa using (Submodule.span K (Set.range basis)).add_mem leftMember rightMember
  · intro scalar value _ valueMember
    simpa using (Submodule.span K (Set.range basis)).smul_mem scalar valueMember

/-- A finite spanning certificate proves equality for every finite label word.
The initial signed comparison is the linear functional `comparison`. -/
theorem comparison_word_eq_zero (operator : Label → V →ₗ[K] V)
    (basis : Index → V) (seed : Seed → V) (comparison : V →ₗ[K] K)
    (contains : ∀ index, seed index ∈ Submodule.span K (Set.range basis))
    (closed : ∀ label index,
      operator label (basis index) ∈ Submodule.span K (Set.range basis))
    (initial : ∀ index, comparison (basis index) = 0)
    (labels : List Label) (index : Seed) :
    comparison (word operator labels (seed index)) = 0 := by
  have annihilated : Submodule.span K (Set.range basis) ≤ LinearMap.ker comparison := by
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    exact initial index
  exact annihilated (word_mem operator _
    (fun label _ => map_mem_span (operator label) basis (closed label)) (contains index) labels)

/-- Finite-dimensional closure always has a finite basis bounded by the
ambient dimension. This existence result makes no compression promise. -/
theorem exists_finite_closed_basis [FiniteDimensional K V]
    (operator : Label → V →ₗ[K] V) (seed : Seed → V) :
    ∃ (size : Nat) (basis : Fin size → V), size ≤ Module.finrank K V ∧
      (∀ index, seed index ∈ Submodule.span K (Set.range basis)) ∧
      (∀ label index, operator label (basis index) ∈ Submodule.span K (Set.range basis)) := by
  let space := orbitSpan operator seed
  let basis := Module.finBasis K space
  have spans : Submodule.span K (Set.range fun index => ((basis index : space) : V)) = space := by
    change Submodule.span K (Set.range (space.subtype ∘ basis)) = space
    rw [Set.range_comp, ← Submodule.map_span, basis.span_eq, Submodule.map_top]
    exact Submodule.range_subtype space
  refine ⟨Module.finrank K space, fun index => (basis index : V),
    Submodule.finrank_le space, ?_, ?_⟩
  · intro index
    rw [spans]
    exact seed_mem_orbitSpan operator seed index
  · intro label index
    rw [spans]
    exact operator_mem_orbitSpan operator seed label (basis index).property

end GameTheory.Math.InvariantObservables
