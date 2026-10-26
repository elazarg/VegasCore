/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-! # Integer directions in rational homogeneous strict systems

A rational projection onto the exact equality kernel lets dense rational
vectors approximate a real feasible direction without disturbing equations.
Finite strict inequalities are open, and a common positive denominator then
turns the rational direction into an integer one.
-/

noncomputable section

namespace GameTheory.Math

open Matrix Filter
open scoped Topology

private theorem exists_kernel_correction {Coordinate Equation : Type*}
    [Fintype Coordinate] [Fintype Equation] [DecidableEq Coordinate]
    (equations : Matrix Equation Coordinate ℚ) :
    ∃ correction : Matrix Coordinate Equation ℚ,
      equations * (1 - correction * equations) = 0 := by
  classical
  let f := equations.mulVecLin
  obtain ⟨inverse, rightInverse⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    f.range_rangeRestrict
  obtain ⟨extension, extensionEq⟩ := inverse.exists_extend
  have repaired : f.comp (extension.comp f) = f := by
    apply LinearMap.ext
    intro vector
    have extended := LinearMap.congr_fun extensionEq (f.rangeRestrict vector)
    change extension (f vector) = inverse (f.rangeRestrict vector) at extended
    change f (extension (f vector)) = f vector
    rw [extended]
    exact congrArg Subtype.val (LinearMap.congr_fun rightInverse (f.rangeRestrict vector))
  let correction := LinearMap.toMatrix' extension
  have matrixF : LinearMap.toMatrix' f = equations := LinearMap.toMatrix'_toLin' equations
  have matrixRepair : equations * (correction * equations) = equations := by
    simpa only [LinearMap.toMatrix'_comp, matrixF] using
      congrArg LinearMap.toMatrix' repaired
  refine ⟨correction, ?_⟩
  rw [Matrix.mul_sub, Matrix.mul_one, matrixRepair, sub_self]

/-- Every real feasible direction of rational homogeneous equations and strict
inequalities admits a rational feasible direction for the exact same system. -/
theorem exists_rational_strict_direction {Coordinate Equation Inequality : Type*}
    [Fintype Coordinate] [Finite Equation] [Finite Inequality]
    (equations : Matrix Equation Coordinate ℚ) (inequalities : Matrix Inequality Coordinate ℚ)
    (direction : Coordinate → ℝ)
    (exactEquations : (equations.map (Rat.castHom ℝ)).mulVec direction = 0)
    (strict : ∀ row, 0 < (inequalities.map (Rat.castHom ℝ)).mulVec direction row) :
    ∃ rational : Coordinate → ℚ, equations.mulVec rational = 0 ∧
      ∀ row, 0 < inequalities.mulVec rational row := by
  classical
  let : Fintype Equation := Fintype.ofFinite Equation
  let : Fintype Inequality := Fintype.ofFinite Inequality
  obtain ⟨correction, repaired⟩ := exists_kernel_correction equations
  let projection : Matrix Coordinate Coordinate ℚ := 1 - correction * equations
  let realProjection := projection.map (Rat.castHom ℝ)
  let realInequalities := inequalities.map (Rat.castHom ℝ)
  have castProjection : realProjection =
      1 - correction.map (Rat.castHom ℝ) * equations.map (Rat.castHom ℝ) := by
    ext row column
    by_cases same : row = column <;>
      simp [realProjection, projection, Matrix.mul_apply, same]
  have fixed : realProjection.mulVec direction = direction := by
    rw [castProjection, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      exactEquations, Matrix.mulVec_zero, sub_zero]
  have continuous : Continuous (fun vector : Coordinate → ℝ =>
      realInequalities.mulVec (realProjection.mulVec vector)) :=
    realInequalities.mulVecLin.continuous_of_finiteDimensional.comp
      realProjection.mulVecLin.continuous_of_finiteDimensional
  have neighborhood : {vector : Coordinate → ℝ |
      ∀ row, 0 < realInequalities.mulVec (realProjection.mulVec vector) row} ∈ 𝓝 direction := by
    apply eventually_all.mpr
    intro row
    exact (continuous.tendsto direction |>.apply_nhds row).eventually_const_lt
      (by simpa only [fixed] using strict row)
  have dense : DenseRange (fun vector : Coordinate → ℚ => fun column => (vector column : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨approximation, positive⟩ := dense.mem_nhds neighborhood
  refine ⟨projection.mulVec approximation, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, show equations * projection = 0 from repaired, Matrix.zero_mulVec]
  · intro row
    have castProjectionValue : (fun column => ((projection.mulVec approximation) column : ℝ)) =
        realProjection.mulVec (fun column => (approximation column : ℝ)) :=
      funext fun column => (Rat.castHom ℝ).map_mulVec projection approximation column
    have castPositive :
        0 < ((inequalities.mulVec (projection.mulVec approximation) row : ℚ) : ℝ) := by
      change 0 < (Rat.castHom ℝ) ((inequalities.mulVec (projection.mulVec approximation)) row)
      rw [RingHom.map_mulVec]
      change 0 < realInequalities.mulVec
        (fun column => ((projection.mulVec approximation) column : ℝ)) row
      rw [castProjectionValue]
      exact positive row
    exact_mod_cast castPositive

/-- Clearing a common positive denominator preserves every homogeneous equation
and every strict inequality, yielding an integer certificate direction. -/
theorem exists_integer_strict_direction {Coordinate Equation Inequality : Type*}
    [Fintype Coordinate] [Finite Equation] [Finite Inequality]
    (equations : Matrix Equation Coordinate ℚ) (inequalities : Matrix Inequality Coordinate ℚ)
    (direction : Coordinate → ℝ)
    (exactEquations : (equations.map (Rat.castHom ℝ)).mulVec direction = 0)
    (strict : ∀ row, 0 < (inequalities.map (Rat.castHom ℝ)).mulVec direction row) :
    ∃ integer : Coordinate → ℤ, equations.mulVec (fun coordinate => (integer coordinate : ℚ)) = 0 ∧
      ∀ row, 0 < inequalities.mulVec (fun coordinate => (integer coordinate : ℚ)) row := by
  obtain ⟨rational, exactRational, strictRational⟩ :=
    exists_rational_strict_direction equations inequalities direction exactEquations strict
  obtain ⟨denominator, numerators⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) rational
  choose integer scaled using numerators
  have vectorEq : (fun coordinate => (integer coordinate : ℚ)) =
      (denominator.val : ℚ) • rational := funext scaled
  refine ⟨integer, ?_, ?_⟩
  · rw [vectorEq, Matrix.mulVec_smul, exactRational, smul_zero]
  · intro row
    rw [vectorEq, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast denominator.prop) (strictRational row)

end GameTheory.Math
