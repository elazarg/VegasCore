/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.PriorityChoice
import GameTheoryExtensions.Core.RegularChoice

/-! # Regular priority mixtures need not preserve relative odds

The two rankings are A < C < B and C < B < A, with A=0, C=1, B=2.
An equal mixture selects A/B before insertion and A/C after insertion.
This is the strict separation used in the inclusion design.
-/

noncomputable section

namespace GameTheoryExtensionsTests.RegularChoice

open GameTheory GameTheory.Math.Probability

def secondRank : Fin 3 → Nat := fun candidate =>
  if candidate = 0 then 2 else if candidate = 1 then 0 else 1

theorem secondRank_injective : Function.Injective secondRank := by decide

abbrev firstOrder : LinearOrder (Fin 3) := inferInstance
abbrev secondOrder : LinearOrder (Fin 3) := LinearOrder.lift' secondRank secondRank_injective

def priorities : FinDist (LinearOrder (Fin 3)) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure firstOrder) (FinDist.pure secondOrder)

def before := PriorityChoice.law priorities {0, 2}
def after := PriorityChoice.law priorities (insert 1 {0, 2})

theorem before_eq : before = FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (some 0)) (FinDist.pure (some 2)) := by
  have first : PriorityChoice.choose firstOrder {0, 2} = some 0 := by decide
  have second : PriorityChoice.choose secondOrder {0, 2} = some 2 := by decide
  simp only [before, PriorityChoice.law, priorities, FinDist.map_mix, FinDist.map_pure,
    first, second]

theorem after_eq : after = FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (some 0)) (FinDist.pure (some 1)) := by
  have first : PriorityChoice.choose firstOrder (insert 1 {0, 2}) = some 0 := by decide
  have second : PriorityChoice.choose secondOrder (insert 1 {0, 2}) = some 1 := by decide
  simp only [after, PriorityChoice.law, priorities, FinDist.map_mix, FinDist.map_pure,
    first, second]

theorem regular : before.RegularAt after (some 1) :=
  PriorityChoice.law_regular_insert priorities {0, 2} 1

/-- No fixed mixture with the original retained law gives this selection. -/
theorem not_fixed_mixture : ¬ ∃ (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1),
    after = FinDist.mix weight nonnegative atMostOne (FinDist.pure (some 1)) before := by
  rintro ⟨weight, nonnegative, atMostOne, same⟩
  have fresh := congrArg (fun law => law.prob (some 1)) same
  have old := congrArg (fun law => law.prob (some 0)) same
  rw [after_eq, before_eq] at fresh old
  norm_num [FinDist.prob_mix, FinDist.prob_pure_eq_ite] at fresh old
  linarith

end GameTheoryExtensionsTests.RegularChoice
