/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.IncentiveCone

/-! # Incentive implication can use a joint restriction on players' utilities

Bob prefers `false` to `true` exactly when Alice prefers `true` to `false`
if the utilities sum to zero at each outcome. The two incentive differences
occupy different player coordinates, but become equal after projection onto
the joint zero-sum utility subspace. Their unrestricted implication fails.

This checks incentive constraints, without asserting an equilibrium theorem
for a runtime or identifying playerwise utility subspaces with the joint one.
-/

noncomputable section

namespace GameTheoryExtensionsTests.CoupledIncentives

open GameTheory GameTheory.Math.Probability

abbrev Coordinate := Fin 2 × Bool

/-- The restriction couples the two players at every public outcome. -/
def zeroSumUtilities : Submodule ℝ (EuclideanSpace ℝ Coordinate) where
  carrier := {utility | ∀ outcome, utility (0, outcome) + utility (1, outcome) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro first second firstZero secondZero outcome
    change first (0, outcome) + second (0, outcome) +
      (first (1, outcome) + second (1, outcome)) = 0
    linarith [firstZero outcome, secondZero outcome]
  smul_mem' := by
    intro amount utility zeroSum outcome
    change amount * utility (0, outcome) + amount * utility (1, outcome) = 0
    rw [← mul_add, zeroSum outcome, mul_zero]

def source : Unit → IncentiveComparison Coordinate :=
  fun _ => ⟨FinDist.pure (1, false), FinDist.pure (1, true)⟩

def target : IncentiveComparison Coordinate :=
  ⟨FinDist.pure (0, true), FinDist.pure (0, false)⟩

theorem projected_differences_equal :
    zeroSumUtilities.orthogonalProjectionOnto target.difference =
      zeroSumUtilities.orthogonalProjectionOnto (source ()).difference := by
  rw [IncentiveComparison.projected_difference_eq_iff]
  intro utility
  simp only [target, source, FinDist.expect_pure]
  have atFalse := utility.property false
  have atTrue := utility.property true
  change utility.val (0, true) - utility.val (0, false) =
    utility.val (1, false) - utility.val (1, true)
  linarith

theorem target_in_joint_cone :
    zeroSumUtilities.orthogonalProjectionOnto target.difference ∈
      IncentiveComparison.coneWithin zeroSumUtilities source := by
  rw [projected_differences_equal]
  exact IncentiveComparison.projected_difference_mem_coneWithin zeroSumUtilities source ()

theorem preserves_within_zeroSum (utility : zeroSumUtilities)
    (respected : (source ()).Holds (WithLp.ofLp utility.val)) :
    target.Holds (WithLp.ofLp utility.val) :=
  (IncentiveComparison.mem_coneWithin_iff zeroSumUtilities source target).mp
    target_in_joint_cone utility (fun _ => respected)

def separatingUtility (coordinate : Coordinate) : ℝ :=
  if coordinate = (0, false) then 1 else 0

theorem unrestricted_source_holds : (source ()).Holds separatingUtility := by
  norm_num [source, IncentiveComparison.Holds, separatingUtility]

theorem unrestricted_target_fails : ¬ target.Holds separatingUtility := by
  norm_num [target, IncentiveComparison.Holds, separatingUtility]

theorem target_outside_unrestricted_cone :
    target.difference ∉ IncentiveComparison.cone source := by
  intro included
  exact unrestricted_target_fails
    ((IncentiveComparison.mem_cone_iff source target).mp included
      separatingUtility (fun _ => unrestricted_source_holds))

end GameTheoryExtensionsTests.CoupledIncentives
