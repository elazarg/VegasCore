/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryChoiceFloor
import Vegas.Game.SourceServiceGeometricTiming

/-! # Choosing native noise after the actual auxiliary source floors -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Filter

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Raw noise may be chosen after arbitrary source and slot sequences. No
lower bound on their decay rates is required. The same noise handles the
binding-send product and repeated binding waiting factors at finite depth. -/
theorem exists_phase_repair_noise (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (source : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : ∀ n, (source n).IsFullyMixed)
    (slot : ℕ → ℝ) (slotPositive : ∀ n, 0 < slot n)
    (capacity : ℝ) (capacityNonnegative : 0 ≤ capacity) (depth : ℕ) :
    ∃ (floor noise : ℕ → ℝ),
      (∀ n, 0 < floor n) ∧ (∀ n, floor n ≤ 1) ∧
      (∀ n who (site : setup.commitRecoveryModel.InformationSite who)
        (choice : setup.commitRecoveryModel.Choice who site.1),
        floor n ≤ ((source n).strategy who site.1 choice).toReal) ∧
      (∀ n, 0 < noise n) ∧ (∀ n, noise n < 1 / 2) ∧
      Tendsto noise atTop (nhds 0) ∧
      Tendsto (fun n => noise n / floor n) atTop (nhds 0) ∧
      Tendsto (fun n => noise n *
        (capacity / ((1 - noise n) * slot n * floor n)) ^ depth) atTop (nhds 0) ∧
      Tendsto (fun n => (1 + noise n / ((1 - noise n) * floor n)) ^ depth)
        atTop (nhds 1) := by
  choose floor floorPositive floorBounded floored using
    fun n => setup.exists_commitRecovery_choice_floor finite (source n) (mixed n)
  let base := fun n => (2 * capacity / (slot n * floor n)) ^ depth
  have baseNonnegative (n : ℕ) : 0 ≤ base n :=
    pow_nonneg (div_nonneg (mul_nonneg (by norm_num) capacityNonnegative)
      (mul_pos (slotPositive n) (floorPositive n)).le) depth
  let passage := fun n => min (floor n) (1 / (1 + base n))
  have passagePositive (n : ℕ) : 0 < passage n :=
    lt_min (floorPositive n) (div_pos zero_lt_one (by linarith [baseNonnegative n]))
  obtain ⟨weight, weightPositive, weightSmall, weightVanishes, relative⟩ :=
    exists_deferralWeights_faster passage passagePositive
  let noise := fun n => weight n / 2
  have noisePositive (n : ℕ) : 0 < noise n := div_pos (weightPositive n) (by norm_num)
  have noiseSmall (n : ℕ) : noise n < 1 / 2 := by
    dsimp only [noise]
    exact div_lt_div_of_pos_right (weightSmall n) (by norm_num)
  have noiseVanishes : Tendsto noise atTop (nhds 0) := by
    simpa only [div_zero, zero_div] using weightVanishes.div_const 2
  have noiseRelative : Tendsto (fun n => noise n / passage n) atTop (nhds 0) := by
    have pointwise : (fun n => noise n / passage n) =
        (fun n => (weight n / passage n) / 2) := by
      funext n
      dsimp only [noise]
      ring
    rw [pointwise]
    simpa only [zero_div] using relative.div_const 2
  have floorRelative : Tendsto (fun n => noise n / floor n) atTop (nhds 0) := by
    apply squeeze_zero (fun n => div_nonneg (noisePositive n).le (floorPositive n).le)
      (fun n => div_le_div_of_nonneg_left (noisePositive n).le (passagePositive n)
        (min_le_left _ _)) noiseRelative
  have baseBound (n : ℕ) : passage n * base n ≤ 1 := by
    have denominator : 0 < 1 + base n := by linarith [baseNonnegative n]
    have fraction : (1 / (1 + base n)) * base n ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one denominator]
      linarith
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (baseNonnegative n)).trans fraction
  have productRelative : Tendsto (fun n => noise n *
      (capacity / ((1 - noise n) * slot n * floor n)) ^ depth) atTop (nhds 0) := by
    have denominatorPositive (n : ℕ) : 0 < (1 - noise n) * slot n * floor n :=
      mul_pos (mul_pos (by linarith [noiseSmall n]) (slotPositive n)) (floorPositive n)
    apply squeeze_zero (fun n => mul_nonneg (noisePositive n).le
      (pow_nonneg (div_nonneg capacityNonnegative (denominatorPositive n).le) depth))
        (fun n => ?_) noiseRelative
    have factorPositive : 0 < slot n * floor n := mul_pos (slotPositive n) (floorPositive n)
    have denominator := denominatorPositive n
    have single : capacity / ((1 - noise n) * slot n * floor n) ≤
        2 * capacity / (slot n * floor n) := by
      rw [div_le_div_iff₀ denominator factorPositive]
      nlinarith [mul_nonneg capacityNonnegative factorPositive.le, noiseSmall n]
    have powered := pow_le_pow_left₀ (by positivity) single depth
    apply (mul_le_mul_of_nonneg_left powered (noisePositive n).le).trans
    rw [le_div_iff₀ (passagePositive n)]
    have scaled := mul_le_mul_of_nonneg_left (baseBound n) (noisePositive n).le
    dsimp only [base] at scaled
    nlinarith only [scaled]
  have waiting : Tendsto (fun n => noise n / ((1 - noise n) * floor n))
      atTop (nhds 0) := by
    have denominator : Tendsto (fun n => 1 - noise n) atTop (nhds (1 : ℝ)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub noiseVanishes
    have ratio := floorRelative.div denominator one_ne_zero
    have pointwise : (fun n => noise n / ((1 - noise n) * floor n)) =
        (fun n => (noise n / floor n) / (1 - noise n)) := by
      funext n
      calc
        noise n / ((1 - noise n) * floor n) =
            noise n / (floor n * (1 - noise n)) := by congr 1; ring
        _ = (noise n / floor n) / (1 - noise n) :=
          (div_div (noise n) (floor n) (1 - noise n)).symm
    have application : ((fun n => noise n / floor n) / (fun n => 1 - noise n)) =
        (fun n => (noise n / floor n) / (1 - noise n)) := by
      funext n
      rfl
    rw [application] at ratio
    rw [pointwise]
    simpa only [zero_div] using ratio
  refine ⟨floor, noise, floorPositive, floorBounded, floored, noisePositive, noiseSmall,
    noiseVanishes, floorRelative, productRelative, ?_⟩
  simpa only [add_zero, one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).add waiting).pow depth

end Vegas
