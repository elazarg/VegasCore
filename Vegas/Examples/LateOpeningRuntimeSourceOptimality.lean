/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSourceBeliefs

/-! # The unique optimal answer under the source posterior

With an independent uniform private label, the safe answer pays two fifths,
whereas each label guess pays at most one third. Randomizing cannot remove
this strict gap: a maximizing answer law is the point mass on the safe answer.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSource

open SourceProgram GameTheory.Math.Probability GameTheory.Protocol

def bobUniformAnswerValue (reward : ℝ) (bit : Bool) (answer : Answer) : ℝ :=
  expect (PMF.uniformOfFintype (Fin 3)) (fun label =>
    grossUtility reward ((bit, label),
      publicOutcome program (finalState bit label true answer true)) bob)

theorem bobUniformAnswerValue_safe (reward : ℝ) (bit : Bool) :
    bobUniformAnswerValue reward bit safe = 2 / 5 := by
  rw [bobUniformAnswerValue, bob_uniform_success_value]
  rfl

theorem bobUniformAnswerValue_le_safe (reward : ℝ) (bit : Bool) (answer : Answer) :
    bobUniformAnswerValue reward bit answer ≤ 2 / 5 := by
  rw [bobUniformAnswerValue, bob_uniform_success_value]
  split_ifs <;> norm_num

theorem bobUniformAnswerValue_lt_safe (reward : ℝ) (bit : Bool) (answer : Answer)
    (different : answer ≠ safe) : bobUniformAnswerValue reward bit answer < 2 / 5 :=
  bob_safe_strictly_best reward bit answer different

theorem bob_answer_law_value_le_safe (reward : ℝ) (bit : Bool) (answers : PMF Answer) :
    expect answers (bobUniformAnswerValue reward bit) ≤ 2 / 5 := by
  calc
    _ ≤ expect answers (fun _ => (2 / 5 : ℝ)) :=
      expect_mono (fun answer _ => bobUniformAnswerValue_le_safe reward bit answer)
        (payoffIntegrable_of_finite _ _) (payoffIntegrable_constant _ _)
    _ = _ := expect_constant _ _

/-- Every answer distribution attaining the source's safe value is the
safe point mass. This controls arbitrary randomization over legal answers. -/
theorem bob_answer_law_eq_pure_safe_of_value_ge (reward : ℝ) (bit : Bool)
    (answers : PMF Answer) (optimal : 2 / 5 ≤ expect answers (bobUniformAnswerValue reward bit)) :
    answers = PMF.pure safe := by
  have value : expect answers (bobUniformAnswerValue reward bit) = 2 / 5 :=
    le_antisymm (bob_answer_law_value_le_safe reward bit answers) optimal
  apply pmf_eq_pure_of_support_subset_singleton
  intro answer supported
  have attained := expect_eq_const_of_le_on_support answers
    (bobUniformAnswerValue reward bit) (2 / 5) (payoffIntegrable_of_finite _ _)
    (fun other _ => bobUniformAnswerValue_le_safe reward bit other) value answer supported
  apply Set.mem_singleton_iff.mpr
  by_contra different
  exact (bobUniformAnswerValue_lt_safe reward bit answer different).ne attained

theorem bob_answer_law_value_eq_safe_iff (reward : ℝ) (bit : Bool) (answers : PMF Answer) :
    expect answers (bobUniformAnswerValue reward bit) = 2 / 5 ↔ answers = PMF.pure safe := by
  constructor
  · intro value
    exact bob_answer_law_eq_pure_safe_of_value_ge reward bit answers value.ge
  · rintro rfl
    rw [expect_pure, bobUniformAnswerValue_safe]

/-- The payoff loss is at least one fifteenth times the probability of
using an unsafe answer. This gives a quantitative version of uniqueness. -/
theorem bob_answer_law_value_bound (reward : ℝ) (bit : Bool) (answers : PMF Answer) :
    expect answers (bobUniformAnswerValue reward bit) ≤
      2 / 5 - (1 - (answers safe).toReal) / 15 := by
  classical
  have pointwise (answer : Answer) : bobUniformAnswerValue reward bit answer ≤
      1 / 3 + if safe = answer then (1 / 15 : ℝ) else 0 := by
    by_cases same : safe = answer
    · subst answer
      rw [bobUniformAnswerValue_safe]
      norm_num
    · rw [bobUniformAnswerValue, bob_uniform_success_value]
      have nonzero : answer.val ≠ 0 := by
        intro zero
        apply same
        apply Subtype.ext
        exact zero.symm
      simp only [nonzero, same, ite_false]
      split_ifs <;> norm_num
  have bound := expect_mono (fun answer _ => pointwise answer)
    (payoffIntegrable_of_finite answers (bobUniformAnswerValue reward bit))
    (payoffIntegrable_of_finite answers (fun answer =>
      1 / 3 + if safe = answer then (1 / 15 : ℝ) else 0))
  rw [expect_add_of_finite, expect_constant, expect_ite_eq] at bound
  linarith

theorem bob_answer_law_safe_probability_of_near_optimal (reward : ℝ) (bit : Bool)
    (answers : PMF Answer) (error : ℝ)
    (nearOptimal : 2 / 5 - error ≤ expect answers (bobUniformAnswerValue reward bit)) :
    1 - 15 * error ≤ (answers safe).toReal := by
  have bound := bob_answer_law_value_bound reward bit answers
  linarith

end Vegas.Examples.LateOpeningRuntimeSource
