/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.IncentiveCone
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform

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
  fun _ => ⟨PMF.pure true, PMF.pure false⟩

def target : IncentiveComparison Bool :=
  ⟨(PMF.uniformOfFintype _), PMF.pure false⟩

theorem target_difference : target.difference = (1 / 2 : ℝ) • (source ()).difference := by
  ext outcome
  cases outcome <;> norm_num [target, source, IncentiveComparison.difference,
    toReal_uniformOfFintype_apply, toReal_pure_apply]

theorem target_in_cone : target.difference ∈ IncentiveComparison.cone source := by
  rw [target_difference]
  exact (IncentiveComparison.cone source).smul_mem
    (IncentiveComparison.difference_mem_cone source ()) (by norm_num)

theorem preserves_incentive (utility : Bool → ℝ) (respected : (source ()).Holds utility) :
    target.Holds utility :=
  (IncentiveComparison.mem_cone_iff source target).mp target_in_cone utility (fun _ => respected)

theorem no_prescribed_root_mixture (roots : PMF Unit) :
    target.prescribed ≠ roots.bind (fun root => (source root).prescribed) := by
  intro same
  have mass := congrArg (fun law => (law true).toReal) same
  norm_num [target, source, toReal_uniformOfFintype_apply,
    toReal_pure_apply] at mass

end GameTheoryExtensionsTests.IncentiveCone
