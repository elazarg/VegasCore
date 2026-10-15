/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingWaitingLaw
import Vegas.Game.CommitRecoveryMissingFloor

/-! # Raw-noise errors in matching physical waiting atoms -/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability

/-- The counted uniform menus can differ. Their entire effect on a waiting
ratio is the explicit raw-noise error above the shared positive waiting mass. -/
theorem waiting_mix_ratio {α β : Type} (firstNoise : PMF α) (secondNoise : PMF β)
    (firstMain : PMF α) (secondMain : PMF β) (first : α) (second : β)
    (same : firstMain first = secondMain second)
    (floor noise : ℝ) (positive : 0 < floor) (nonnegative : 0 ≤ noise) (small : noise < 1)
    (lower : floor ≤ (secondMain second).toReal) :
    let firstMass := (mix noise nonnegative small.le firstNoise firstMain first).toReal
    let secondMass := (mix noise nonnegative small.le secondNoise secondMain second).toReal
    firstMass - secondMass = noise * ((firstNoise first).toReal -
      (secondNoise second).toReal) ∧
    (1 - noise) * floor ≤ secondMass ∧
    firstMass ≤ (1 + noise / ((1 - noise) * floor)) * secondMass := by
  intro firstMass secondMass
  have firstNonnegative := ENNReal.toReal_nonneg (a := firstNoise first)
  have secondNonnegative := ENNReal.toReal_nonneg (a := secondNoise second)
  have firstBounded : (firstNoise first).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ _)
  have denominator : 0 < (1 - noise) * floor := mul_pos (sub_pos.mpr small) positive
  have identity : firstMass - secondMass = noise * ((firstNoise first).toReal -
      (secondNoise second).toReal) := by
    dsimp only [firstMass, secondMass]
    rw [mix_apply_toReal, mix_apply_toReal, same]
    ring
  have bounded : (1 - noise) * floor ≤ secondMass := by
    dsimp only [secondMass]
    rw [mix_apply_toReal]
    nlinarith [mul_le_mul_of_nonneg_left lower (sub_nonneg.mpr small.le)]
  refine ⟨identity, bounded, ?_⟩
  have difference : firstMass ≤ secondMass + noise := by nlinarith
  have error : noise ≤ noise / ((1 - noise) * floor) * secondMass := by
    rw [div_mul_eq_mul_div, le_div_iff₀ denominator]
    exact mul_le_mul_of_nonneg_left bounded nonnegative
  nlinarith

end Vegas
