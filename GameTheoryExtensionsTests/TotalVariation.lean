/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Total variation transports two arbitrary unclassified outputs -/

noncomputable section

namespace GameTheoryExtensionsTests.TotalVariation

open GameTheory.Math.Probability

private def law : PMF (Option Bool) :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure none)
    (mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (some false)) (PMF.pure (some true)))

private def classify : Option Bool → Option Unit
  | none => some ()
  | some _ => none

private def read (point : Option Bool) : Bool := point.getD false

private theorem class_law : law.map classify =
    mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure (some ())) (PMF.pure none) := by
  simp [law, mix_map, PMF.pure_map, classify, mix_self]

private theorem class_close :
    PMF.WithinTV (1 / 2) (law.map classify) ((PMF.pure ()).map some) := by
  have dominated (outcome : Option Unit) :
      (1 / 2 : ℝ) * ((PMF.pure (some ())) outcome).toReal ≤
        ((law.map classify) outcome).toReal := by
    rw [class_law, mix_apply_toReal]
    nlinarith [ENNReal.toReal_nonneg (a := (PMF.pure none : PMF (Option Unit)) outcome)]
  have bound := PMF.WithinTV.of_domination (PMF.pure (some ())) (law.map classify)
    (1 / 2) (by norm_num) dominated
  simpa only [PMF.pure_map, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using bound.symm

/-- Two distinct unclassified inputs share the absent class but have different
actual outputs. No factorization of their outputs through the absent class is
assumed by the transport theorem. -/
theorem two_unclassified_outputs :
    classify (some false) = classify (some true) ∧ read (some false) ≠ read (some true) := by
  simp [classify, read]

theorem output_close :
    PMF.WithinTV (1 / 2) (law.map read) ((PMF.pure ()).map fun _ => false) := by
  apply withinTV_map_of_partial_classes law read classify (fun _ => false) (PMF.pure ()) _
    class_close
  intro point _ classValue reading
  cases point with
  | none => rfl
  | some bit => simp [classify] at reading

theorem interval_payoff_bound :
    |expect (law.map read) (fun bit => if bit then (3 : ℝ) else -1) -
      expect ((PMF.pure ()).map fun _ => false) (fun bit => if bit then (3 : ℝ) else -1)| ≤ 2 := by
  have bound := output_close.abs_expect_sub_le_interval (fun bit => if bit then (3 : ℝ) else -1)
    (-1) 4 (by intro bit _; cases bit <;> norm_num)
  norm_num at bound ⊢
  exact bound

theorem actual_true_mass : ((law.map read) true).toReal = 1 / 4 := by
  norm_num [law, mix_map, PMF.pure_map, mix_apply_toReal, read, PMF.pure_apply]

end GameTheoryExtensionsTests.TotalVariation
