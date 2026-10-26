/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.OrderClosed

/-! # Finite and divergent linear constraints admit an affine ray

Project the approximate solutions onto the kernel of the finite-limit map
using a continuous right inverse on its closed range. The correction converges,
so the strict constraints remain eventually positive. No separation theorem or
linear-programming solver is needed.
-/

noncomputable section

namespace GameTheory.Math

open Filter
open scoped Topology

/-- A sequence satisfying finite and positive-infinite linear limits gives an
exact intercept and a homogeneous strict direction. The resulting affine ray
preserves the finite equations and diverges along every strict row. -/
theorem exists_affine_ray
    {Coordinate Equation Inequality : Type} [Finite Coordinate] [Finite Equation]
    [Finite Inequality]
    (equations : (Coordinate → ℝ) →ₗ[ℝ] (Equation → ℝ))
    (inequalities : (Coordinate → ℝ) →ₗ[ℝ] (Inequality → ℝ))
    (sequence : Nat → Coordinate → ℝ) (limit : Equation → ℝ)
    (finiteLimit : Tendsto (fun n => equations (sequence n)) atTop (𝓝 limit))
    (infiniteLimit : ∀ row, Tendsto (fun n => inequalities (sequence n) row) atTop atTop) :
    ∃ intercept direction, equations intercept = limit ∧ equations direction = 0 ∧
      ∀ row, 0 < inequalities direction row := by
  classical
  have inRange : limit ∈ equations.range :=
    equations.range.closed_of_finiteDimensional.mem_of_tendsto finiteLimit
      (Eventually.of_forall fun n => equations.mem_range_self (sequence n))
  let rangeLimit : equations.range := ⟨limit, inRange⟩
  obtain ⟨inverse, rightInverse⟩ := equations.rangeRestrict.exists_rightInverse_of_surjective
    equations.range_rangeRestrict
  have inverse_eq (value : equations.range) : equations (inverse value) = value :=
    congrArg Subtype.val (LinearMap.congr_fun rightInverse value)
  let intercept := inverse rangeLimit
  have intercept_eq : equations intercept = limit := inverse_eq rangeLimit
  have correctionLimit :
      Tendsto (fun n => inverse (equations.rangeRestrict (sequence n))) atTop (𝓝 intercept) :=
    (inverse.continuous_of_finiteDimensional.tendsto rangeLimit).comp
      (tendsto_subtype_rng.mpr finiteLimit)
  have positive : ∀ᶠ n in atTop, ∀ row,
      0 < inequalities (sequence n - inverse (equations.rangeRestrict (sequence n))) row := by
    apply eventually_all.mpr
    intro row
    have correction :=
      ((inequalities.continuous_of_finiteDimensional.tendsto intercept).comp
        correctionLimit).apply_nhds row
    filter_upwards [infiniteLimit row |>.eventually_gt_atTop (inequalities intercept row + 1),
      correction.eventually_lt_const (lt_add_one _)] with n above below
    simpa only [map_sub, Pi.sub_apply, Function.comp_apply] using
      sub_pos.mpr (below.trans above)
  obtain ⟨n, allPositive⟩ := positive.exists
  refine ⟨intercept, sequence n - inverse (equations.rangeRestrict (sequence n)),
    intercept_eq, ?_, allPositive⟩
  rw [map_sub, inverse_eq]
  exact sub_self _

end GameTheory.Math
