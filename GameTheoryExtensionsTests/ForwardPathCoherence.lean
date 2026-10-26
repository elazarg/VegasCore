/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Tactic

/-! # Closed paths do not test coherence of parallel forward paths

Two edges of an acyclic quiver act by identity and translation. Every closed
path acts trivially, but there is no exact family of compatible real values.
This concerns a path-coherence criterion, not equilibrium preservation.
-/

namespace GameTheoryExtensionsTests.ForwardPathCoherence

inductive Edge : Bool → Bool → Type
  | direct : Edge false true
  | shifted : Edge false true

instance : Quiver Bool := ⟨Edge⟩

def height (vertex : Bool) : ℕ := if vertex then 1 else 0

/-- Every edge strictly increases height, so a closed path is empty. -/
theorem height_eq_add_length {start finish : Bool} (path : Quiver.Path start finish) :
    height finish = height start + path.length := by
  induction path with
  | nil => simp
  | cons path edge ih =>
    cases edge <;> simp only [height, Bool.false_eq_true, ↓reduceIte,
      Quiver.Path.length_cons] at ih ⊢ <;> omega

theorem closed_path_eq_nil (vertex : Bool) (path : Quiver.Path vertex vertex) :
    path = .nil :=
  path.eq_nil_of_length_zero (by have := height_eq_add_length path; omega)

def edgeMap {start finish : Bool} : (start ⟶ finish) → ℝ → ℝ
  | .direct, value => value
  | .shifted, value => value + 1

def pathMap {start : Bool} : {finish : Bool} → Quiver.Path start finish → ℝ → ℝ
  | _, .nil, value => value
  | _, .cons path edge, value => edgeMap edge (pathMap path value)

/-- All closed-path transports are identity, without any nonempty cycle to test. -/
theorem closed_path_map (vertex : Bool) (path : Quiver.Path vertex vertex) :
    pathMap path = id := by
  rw [closed_path_eq_nil vertex path]
  rfl

theorem parallel_path_maps_differ :
    pathMap (Quiver.Hom.toPath Edge.direct) ≠
      pathMap (Quiver.Hom.toPath Edge.shifted) := by
  intro same
  have atZero := congrFun same 0
  change (0 : ℝ) = 0 + 1 at atZero
  norm_num at atZero

/-- Trivial closed-path transport therefore does not guarantee an exact section. -/
theorem no_compatible_family :
    ¬ ∃ family : Bool → ℝ, ∀ {start finish : Bool} (edge : start ⟶ finish),
      family finish = edgeMap edge (family start) := by
  rintro ⟨family, compatible⟩
  have direct := compatible Edge.direct
  have shifted := compatible Edge.shifted
  dsimp [edgeMap] at direct shifted
  linarith

end GameTheoryExtensionsTests.ForwardPathCoherence
