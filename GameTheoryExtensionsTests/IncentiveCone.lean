/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.IncentiveCone

/-! # Incentive preservation without prescribed-law matching

The source comparison is certain success versus certain failure. The target
comparison is a fair success chance versus certain failure. Both enforce the
same utility ordering, although their prescribed laws differ. A distribution
over copies of the only source prescribed law cannot explain the target law.
-/

noncomputable section

namespace GameTheoryExtensionsTests.IncentiveCone

open GameTheory GameTheory.Math.Probability

def source : Unit → IncentiveComparison Bool :=
  fun _ => ⟨FinDist.pure true, FinDist.pure false⟩

def target : IncentiveComparison Bool :=
  ⟨FinDist.uniformOfFintype, FinDist.pure false⟩

theorem target_difference : target.difference = (1 / 2 : ℝ) • (source ()).difference := by
  ext outcome
  cases outcome <;> norm_num [target, source, IncentiveComparison.difference,
    FinDist.prob_uniformOfFintype, FinDist.prob_pure_eq_ite]

theorem target_in_cone : target.difference ∈ IncentiveComparison.cone source := by
  rw [target_difference]
  exact (IncentiveComparison.cone source).smul_mem
    (IncentiveComparison.difference_mem_cone source ()) (by norm_num)

theorem preserves_incentive (utility : Bool → ℝ) (respected : (source ()).Holds utility) :
    target.Holds utility :=
  (IncentiveComparison.mem_cone_iff source target).mp target_in_cone utility (fun _ => respected)

theorem no_prescribed_root_mixture (roots : FinDist Unit) :
    target.prescribed ≠ roots.bind (fun root => (source root).prescribed) := by
  intro same
  have mass := congrArg (fun law => law.prob true) same
  norm_num [target, source, FinDist.prob_uniformOfFintype,
    FinDist.prob_pure_eq_ite] at mass

end GameTheoryExtensionsTests.IncentiveCone
