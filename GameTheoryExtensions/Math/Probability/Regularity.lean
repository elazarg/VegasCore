/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist

/-! # Moving probability only toward a distinguished outcome

Regular insertion decreases the probability of every old outcome. It need not
preserve their relative odds. These laws concern finite distributions and do
not assume any network or incentive model.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α β γ : Type*}

/-- Only the distinguished outcome may gain probability. -/
def RegularAt (before after : FinDist α) (fresh : α) : Prop :=
  ∀ value, value ≠ fresh → after.prob value ≤ before.prob value

theorem RegularAt.refl (law : FinDist α) (fresh : α) : law.RegularAt law fresh :=
  fun _ _ => le_rfl

theorem RegularAt.trans {first second third : FinDist α} {fresh : α}
    (left : first.RegularAt second fresh) (right : second.RegularAt third fresh) :
    first.RegularAt third fresh :=
  fun value different => (right value different).trans (left value different)

/-- Pointwise weighted inequalities compare expectations over different laws. -/
theorem expect_le_of_prob_mul_le (first second : FinDist α) (f g : α → ℝ)
    (bound : ∀ value, first.prob value * f value ≤ second.prob value * g value) :
    first.expect f ≤ second.expect g :=
  (first.summable_prob_mul f).tsum_le_tsum bound (second.summable_prob_mul g)

/-- The gain equals removed probability times the gap from the fresh value. -/
theorem expect_gain_eq (before after : FinDist α) (fresh : α) (utility : α → ℝ) :
    after.expect utility - before.expect utility =
      ∑' value, (before.prob value - after.prob value) *
        (utility fresh - utility value) := by
  calc
    _ = before.expect (fun value => utility fresh - utility value) -
        after.expect (fun value => utility fresh - utility value) := by
      rw [expect_sub, expect_sub, expect_const, expect_const]
      ring
    _ = _ := by
      rw [expect, expect, ← Summable.tsum_sub
        (before.summable_prob_mul _) (after.summable_prob_mul _)]
      apply tsum_congr
      intro value
      ring

/-- Moving mass toward a utility maximum cannot reduce expected utility. -/
theorem RegularAt.expect_le {before after : FinDist α} {fresh : α}
    (regular : before.RegularAt after fresh) (utility : α → ℝ)
    (optimal : ∀ value, utility value ≤ utility fresh) :
    before.expect utility ≤ after.expect utility := by
  have deficits := expect_le_of_prob_mul_le after before
    (fun value => utility fresh - utility value)
    (fun value => utility fresh - utility value) (fun value => by
      by_cases same : value = fresh
      · simp [same]
      · exact mul_le_mul_of_nonneg_right (regular value same)
          (sub_nonneg.mpr (optimal value)))
  simp only [expect_sub, expect_const] at deficits
  linarith

/-- Regularity is exactly the condition that improves every utility whose
maximum includes the distinguished outcome. This is a local characterization. -/
theorem regularAt_iff_expect_le (before after : FinDist α) (fresh : α) :
    before.RegularAt after fresh ↔
      ∀ utility : α → ℝ, (∀ value, utility value ≤ utility fresh) →
        before.expect utility ≤ after.expect utility := by
  classical
  constructor
  · exact fun regular utility optimal => regular.expect_le utility optimal
  · intro improves value different
    let indicator : α → ℝ := fun candidate => if value = candidate then 1 else 0
    have maximum : ∀ candidate, -indicator candidate ≤ -indicator fresh := by
      intro candidate
      simp only [indicator, ite_eq_right different, neg_zero]
      split <;> norm_num
    have bound := improves (fun candidate => -indicator candidate) maximum
    have negated (law : FinDist α) :
        law.expect (fun candidate => -indicator candidate) = -law.expect indicator := by
      simpa only [zero_sub, expect_const] using
        (expect_sub law (fun _ => 0) indicator)
    rw [negated, negated] at bound
    have beforeIndicator : before.expect indicator = before.prob value := by
      simpa [indicator, map_id] using (prob_map id before value).symm
    have afterIndicator : after.expect indicator = after.prob value := by
      simpa [indicator, map_id] using (prob_map id after value).symm
    rw [beforeIndicator, afterIndicator] at bound
    linarith

/-- If a coupled choice changes, it changes to the fresh candidate. -/
theorem regularAt_of_coupling (law : FinDist β) (before after : β → α) (fresh : α)
    (stable : ∀ draw ∈ law.support, after draw = before draw ∨ after draw = fresh) :
    (law.map before).RegularAt (law.map after) fresh := by
  classical
  intro value different
  rw [prob_map, prob_map]
  apply expect_mono
  intro draw member
  rcases stable draw member with same | same
  · rw [same]
  · simp only [same, ite_eq_right different]
    split <;> norm_num

/-- Randomizing among regular rules preserves regularity. -/
theorem regularAt_bind (law : FinDist β) (before after : β → FinDist α) (fresh : α)
    (regular : ∀ draw ∈ law.support, (before draw).RegularAt (after draw) fresh) :
    (law.bind before).RegularAt (law.bind after) fresh := by
  intro value different
  rw [prob_bind, prob_bind]
  exact expect_mono fun draw member => regular draw member value different

/-- Observing outcomes may merge candidates; regularity still holds. -/
theorem RegularAt.map {before after : FinDist α} {fresh : α}
    (regular : before.RegularAt after fresh) (observe : α → γ) :
    (before.map observe).RegularAt (after.map observe) (observe fresh) := by
  classical
  intro value different
  rw [prob_map, prob_map]
  apply expect_le_of_prob_mul_le
  intro candidate
  by_cases same : value = observe candidate
  · simp only [same, ↓reduceIte, mul_one]
    exact regular candidate (fun equal => different (same.trans (congrArg observe equal)))
  · simp [same]

/-- The fixed-mixture condition is a special case of regularity. -/
theorem regularAt_mix (law : FinDist α) (fresh : α) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    law.RegularAt (mix weight nonnegative atMostOne (pure fresh) law) fresh := by
  intro value different
  rw [prob_mix, prob_pure_of_ne different, mul_zero, zero_add]
  nlinarith [law.prob_nonneg value]

end GameTheory.Math.Probability.FinDist
