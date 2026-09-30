/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

/-! # Moving probability only toward a distinguished outcome

Regular insertion decreases the probability of every old outcome. It need not
preserve their relative odds. These laws concern finite distributions and do
not assume any network or incentive model.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {α β γ : Type*}

/-- Only the distinguished outcome may gain probability. -/
def RegularAt (before after : PMF α) (fresh : α) : Prop :=
  ∀ value, value ≠ fresh → (after value).toReal ≤ (before value).toReal

theorem RegularAt.refl (law : PMF α) (fresh : α) : law.RegularAt law fresh :=
  fun _ _ => le_rfl

theorem RegularAt.trans {first second third : PMF α} {fresh : α}
    (left : first.RegularAt second fresh) (right : second.RegularAt third fresh) :
    first.RegularAt third fresh :=
  fun value different => (right value different).trans (left value different)

/-- Pointwise weighted inequalities compare expectations over different laws. -/
theorem expect_le_of_prob_mul_le (first second : PMF α) (f g : α → ℝ)
    (firstIntegrable : PayoffIntegrable first f) (secondIntegrable : PayoffIntegrable second g)
    (bound : ∀ value, (first value).toReal * f value ≤ (second value).toReal * g value) :
    expect first f ≤ expect second g :=
  firstIntegrable.summable.tsum_le_tsum bound secondIntegrable.summable

/-- The gain equals removed probability times the gap from the fresh value. -/
theorem expect_gain_eq (before after : PMF α) (fresh : α) (utility : α → ℝ)
    (beforeIntegrable : PayoffIntegrable before utility)
    (afterIntegrable : PayoffIntegrable after utility) :
    expect after utility - expect before utility =
      ∑' value, ((before value).toReal - (after value).toReal) *
        (utility fresh - utility value) := by
  have gapBefore := payoffIntegrable_sub (payoffIntegrable_constant before (utility fresh))
    beforeIntegrable
  have gapAfter := payoffIntegrable_sub (payoffIntegrable_constant after (utility fresh))
    afterIntegrable
  calc
    _ = expect before (fun value => utility fresh - utility value) -
        expect after (fun value => utility fresh - utility value) := by
      rw [expect_sub (payoffIntegrable_constant _ _) beforeIntegrable,
        expect_sub (payoffIntegrable_constant _ _) afterIntegrable,
        expect_constant, expect_constant]
      ring
    _ = _ := by
      rw [expect, expect, ← Summable.tsum_sub gapBefore.summable gapAfter.summable]
      apply tsum_congr
      intro value
      ring

/-- Moving mass toward a utility maximum cannot reduce expected utility. -/
theorem RegularAt.expect_le {before after : PMF α} {fresh : α}
    (regular : before.RegularAt after fresh) (utility : α → ℝ)
    (optimal : ∀ value, utility value ≤ utility fresh)
    (beforeIntegrable : PayoffIntegrable before utility)
    (afterIntegrable : PayoffIntegrable after utility) :
    expect before utility ≤ expect after utility := by
  have deficits := expect_le_of_prob_mul_le after before
    (fun value => utility fresh - utility value)
    (fun value => utility fresh - utility value)
    (payoffIntegrable_sub (payoffIntegrable_constant _ _) afterIntegrable)
    (payoffIntegrable_sub (payoffIntegrable_constant _ _) beforeIntegrable) (fun value => by
      by_cases same : value = fresh
      · simp [same]
      · exact mul_le_mul_of_nonneg_right (regular value same)
          (sub_nonneg.mpr (optimal value)))
  rw [expect_sub (payoffIntegrable_constant _ _) afterIntegrable,
    expect_sub (payoffIntegrable_constant _ _) beforeIntegrable,
    expect_constant, expect_constant] at deficits
  linarith

/-- Regularity is exactly the condition that improves every integrable utility
whose maximum includes the distinguished outcome. This is a local
characterization. -/
theorem regularAt_iff_expect_le (before after : PMF α) (fresh : α) :
    before.RegularAt after fresh ↔
      ∀ utility : α → ℝ, (∀ value, utility value ≤ utility fresh) →
        PayoffIntegrable before utility → PayoffIntegrable after utility →
          expect before utility ≤ expect after utility := by
  classical
  constructor
  · exact fun regular utility optimal => regular.expect_le utility optimal
  · intro improves value different
    let indicator : α → ℝ := fun candidate => if value = candidate then 1 else 0
    have maximum : ∀ candidate, -indicator candidate ≤ -indicator fresh := by
      intro candidate
      simp only [indicator, ite_eq_right different, neg_zero]
      split <;> norm_num
    have bounded (law : PMF α) : PayoffIntegrable law (fun candidate => -indicator candidate) :=
      payoffIntegrable_of_bounded law _ (C := 1) fun candidate => by
        simp only [indicator, abs_neg]
        split <;> norm_num
    have bound := improves (fun candidate => -indicator candidate) maximum
      (bounded before) (bounded after)
    rw [expect_neg, expect_neg, expect_ite_eq, expect_ite_eq, mul_one, mul_one] at bound
    linarith

/-- If a coupled choice changes, it changes to the fresh candidate. -/
theorem regularAt_of_coupling (law : PMF β) (before after : β → α) (fresh : α)
    (stable : ∀ draw ∈ law.support, after draw = before draw ∨ after draw = fresh) :
    (law.map before).RegularAt (law.map after) fresh := by
  classical
  intro value different
  rw [toReal_map_apply, toReal_map_apply]
  apply expect_mono _ (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split <;> norm_num)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split <;> norm_num)
  intro draw member
  rcases stable draw member with same | same
  · rw [same]
  · simp only [same, ite_eq_right different]
    split <;> norm_num

/-- Randomizing among regular rules preserves regularity. -/
theorem regularAt_bind (law : PMF β) (before after : β → PMF α) (fresh : α)
    (regular : ∀ draw ∈ law.support, (before draw).RegularAt (after draw) fresh) :
    (law.bind before).RegularAt (law.bind after) fresh := by
  intro value different
  rw [toReal_bind_apply, toReal_bind_apply]
  exact expect_mono (fun draw member => regular draw member value different)
    (payoffIntegrable_toReal_apply _ _ _) (payoffIntegrable_toReal_apply _ _ _)

/-- Observing outcomes may merge candidates; regularity still holds. -/
theorem RegularAt.map {before after : PMF α} {fresh : α}
    (regular : before.RegularAt after fresh) (observe : α → γ) :
    (before.map observe).RegularAt (after.map observe) (observe fresh) := by
  classical
  intro value different
  rw [toReal_map_apply, toReal_map_apply]
  apply expect_le_of_prob_mul_le _ _ _ _
    (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split <;> norm_num)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split <;> norm_num)
  intro candidate
  by_cases same : value = observe candidate
  · simp only [same, ↓reduceIte, mul_one]
    exact regular candidate (fun equal => different (same.trans (congrArg observe equal)))
  · simp [same]

/-- The fixed-mixture condition is a special case of regularity. -/
theorem regularAt_mix (law : PMF α) (fresh : α) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    law.RegularAt (mix weight nonnegative atMostOne (PMF.pure fresh) law) fresh := by
  intro value different
  rw [mix_apply_toReal, PMF.pure_apply, ite_eq_right different, ENNReal.toReal_zero, mul_zero,
    zero_add]
  nlinarith [ENNReal.toReal_nonneg (a := law value)]

end PMF
