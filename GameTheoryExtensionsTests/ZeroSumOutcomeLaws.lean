/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MatrixGame
import GameTheoryExtensions.Math.Probability.Expectation

/-! # A zero-sum value does not determine the payout law

Each player chooses -1, 0, or 1. The payouts are `(xy, -xy)`. Choosing zero
surely and independently choosing fair signs are both mixed Nash equilibria,
but one pays zero surely and the other pays a nonzero amount surely.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ZeroSumOutcomeLaws

open GameTheory GameTheory.Math.Probability

abbrev Action := Option Bool

def amount : Action → ℝ
  | none => 0
  | some false => -1
  | some true => 1

def matrix (row col : Action) : ℝ := amount row * amount col

abbrev form := MatrixGame.form Action Action

def payout : Action × Action → Fin 2 → ℝ := MatrixGame.utility matrix

theorem zeroSum : IsZeroSum payout := MatrixGame.utility_isZeroSum matrix

def signs : PMF Action :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (some false)) (PMF.pure (some true))

def zeroProfile : Profile form.sig.mixed :=
  MatrixGame.mixedProfile (PMF.pure none) (PMF.pure none)

def signProfile : Profile form.sig.mixed := MatrixGame.mixedProfile signs signs

/-- Every law on the finite outcome carrier integrates every payoff. -/
theorem integrable (law : PMF (Action × Action)) (payoff : Action × Action → ℝ) :
    PayoffIntegrable law payoff :=
  payoffIntegrable_of_finite law payoff

theorem mixed_play (row col : PMF Action) :
    form.mixed.play (MatrixGame.mixedProfile row col) =
      row.bind fun current => col.map fun other => (current, other) := by
  conv_lhs => rw [← Profile.update_eq_self (MatrixGame.mixedProfile row col) 0]
  rw [GameForm.mixed_play_update, MatrixGame.mixedProfile_zero]
  congr 1
  funext current
  rw [MatrixGame.mixedProfile_update_zero, MatrixGame.mixed_play_pure_row]

theorem expectedPayoff (row col : PMF Action) :
    MatrixGame.expectedPayoff matrix row col = expect row amount * expect col amount := by
  rw [(MatrixGame.expectedPayoff_eq_expect_rows matrix row col (integrable _ _)).2]
  change expect row (fun current => expect col (fun other => amount current * amount other)) = _
  simp only [expect_const_mul, expect_mul_const]

@[simp] theorem signs_mean : expect signs amount = 0 := by
  norm_num [signs, expect_mix_of_finite, expect_pure, amount]

theorem centered_nash (law : PMF Action) (mean : expect law amount = 0) :
    IsNash form.mixed (euPreference payout) (MatrixGame.mixedProfile law law) := by
  apply IsSaddlePoint.isNash _ zeroSum
  apply (MatrixGame.isSaddlePoint_iff_guarantees_caps matrix law law).mpr
  refine ⟨integrable _ _, fun col => ⟨integrable _ _, ?_⟩, fun row => ⟨integrable _ _, ?_⟩⟩ <;>
    simp [expectedPayoff, mean]

theorem zero_nash : IsNash form.mixed (euPreference payout) zeroProfile :=
  centered_nash (PMF.pure none) (by simp [amount, expect_pure])

theorem signs_nash : IsNash form.mixed (euPreference payout) signProfile :=
  centered_nash signs signs_mean

def payoutLaw (profile : Profile form.sig.mixed) : PMF (Fin 2 → ℝ) :=
  (form.mixed.play profile).map payout

theorem zero_payoutLaw : payoutLaw zeroProfile = PMF.pure (fun _ => 0) := by
  rw [payoutLaw, zeroProfile, mixed_play]
  simp only [PMF.pure_bind, PMF.pure_map]
  apply congrArg PMF.pure
  funext who
  fin_cases who <;> simp [payout, matrix, amount]

theorem sign_amount_square : expect signs (fun action => amount action ^ 2) = 1 := by
  norm_num [signs, expect_mix_of_finite, expect_pure, amount]

/-- A payout statistic distinguishes the complete laws, even though every
player's expected payout is the same. -/
theorem signs_squared_payout :
    expect (payoutLaw signProfile) (fun result => result 0 ^ 2) = 1 := by
  rw [payoutLaw, signProfile, mixed_play, expect_map,
    expect_bind_tower _ _ _ (integrable _ _)]
  simp only [expect_map, Function.comp_def]
  change expect signs (fun row => expect signs
    (fun col => (amount row * amount col) ^ 2)) = _
  simp only [mul_pow, expect_const_mul, sign_amount_square, mul_one]

theorem payoutLaws_different : payoutLaw zeroProfile ≠ payoutLaw signProfile := by
  intro same
  have observed := congrArg (fun law => expect law (fun result => result 0 ^ 2)) same
  rw [zero_payoutLaw, expect_pure, signs_squared_payout] at observed
  norm_num at observed

theorem equilibrium_values_equal (who : Fin 2) :
    expectedUtility payout who (form.mixed.play zeroProfile) =
      expectedUtility payout who (form.mixed.play signProfile) := by
  have first := zero_nash.isSaddlePoint zeroSum
  have second := signs_nash.isSaddlePoint zeroSum
  fin_cases who
  · exact (first.value_eq second).2.2
  · change expectedUtility payout 1 (form.mixed.play zeroProfile) =
      expectedUtility payout 1 (form.mixed.play signProfile)
    rw [zeroSum.expectedUtility_one, zeroSum.expectedUtility_one, (first.value_eq second).2.2]

theorem same_zeroSum_values_different_payout_laws :
    IsZeroSum payout ∧
    IsNash form.mixed (euPreference payout) zeroProfile ∧
    IsNash form.mixed (euPreference payout) signProfile ∧
    (∀ who, expectedUtility payout who (form.mixed.play zeroProfile) =
      expectedUtility payout who (form.mixed.play signProfile)) ∧
    payoutLaw zeroProfile ≠ payoutLaw signProfile :=
  ⟨zeroSum, zero_nash, signs_nash, equilibrium_values_equal, payoutLaws_different⟩

end GameTheoryExtensionsTests.ZeroSumOutcomeLaws
