/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MatrixGame

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

def signs : FinDist Action :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (some false)) (FinDist.pure (some true))

def zeroProfile : Profile form.sig.mixed :=
  MatrixGame.mixedProfile (FinDist.pure none) (FinDist.pure none)

def signProfile : Profile form.sig.mixed := MatrixGame.mixedProfile signs signs

theorem mixed_play (row col : FinDist Action) :
    form.mixed.play (MatrixGame.mixedProfile row col) = FinDist.product row col := by
  rw [GameForm.mixed_play, ← FinDist.piFin_eq_pi]
  simp [FinDist.piFin, MatrixGame.mixedProfile, MatrixGame.form, FinDist.product,
    Fin.consEquiv, FinDist.map_eq_bind]

theorem expectedPayoff (row col : FinDist Action) :
    MatrixGame.expectedPayoff matrix row col = row.expect amount * col.expect amount := by
  change (form.mixed.play (MatrixGame.mixedProfile row col)).expect
    (fun result => matrix result.1 result.2) = _
  rw [mixed_play, FinDist.expect_product]
  simp only [matrix, FinDist.expect_smul, FinDist.expect_mul_const]

@[simp] theorem signs_mean : signs.expect amount = 0 := by
  norm_num [signs, FinDist.expect_mix, amount]

theorem centered_nash (law : FinDist Action) (mean : law.expect amount = 0) :
    IsNash form.mixed (euPreference payout) (MatrixGame.mixedProfile law law) := by
  apply IsSaddlePoint.isNash _ zeroSum
  apply (MatrixGame.isSaddlePoint_iff_guarantees_caps matrix law law).mpr
  constructor
  · intro col
    simp [expectedPayoff, mean]
  · intro row
    simp [expectedPayoff, mean]

theorem zero_nash : IsNash form.mixed (euPreference payout) zeroProfile :=
  centered_nash (FinDist.pure none) (by simp [amount])

theorem signs_nash : IsNash form.mixed (euPreference payout) signProfile :=
  centered_nash signs signs_mean

def payoutLaw (profile : Profile form.sig.mixed) : FinDist (Fin 2 → ℝ) :=
  (form.mixed.play profile).map payout

theorem zero_payoutLaw : payoutLaw zeroProfile = FinDist.pure (fun _ => 0) := by
  rw [payoutLaw, zeroProfile, mixed_play]
  simp only [FinDist.product, FinDist.pure_bind, FinDist.map_pure]
  apply congrArg FinDist.pure
  funext who
  fin_cases who <;> simp [payout, matrix, amount]

theorem sign_amount_square : signs.expect (fun action => amount action ^ 2) = 1 := by
  norm_num [signs, FinDist.expect_mix, amount]

/-- A payout statistic distinguishes the complete laws, even though every
player's expected payout is the same. -/
theorem signs_squared_payout :
    (payoutLaw signProfile).expect (fun result => result 0 ^ 2) = 1 := by
  rw [payoutLaw, signProfile, mixed_play, FinDist.expect_map, FinDist.expect_product]
  change signs.expect (fun row => signs.expect
    (fun col => (amount row * amount col) ^ 2)) = _
  simp only [mul_pow, FinDist.expect_smul, sign_amount_square, mul_one]

theorem payoutLaws_different : payoutLaw zeroProfile ≠ payoutLaw signProfile := by
  intro same
  have observed := congrArg (fun law => law.expect (fun result => result 0 ^ 2)) same
  rw [zero_payoutLaw, FinDist.expect_pure, signs_squared_payout] at observed
  norm_num at observed

theorem equilibrium_values_equal (who : Fin 2) :
    expectedUtility payout who (form.mixed.play zeroProfile) =
      expectedUtility payout who (form.mixed.play signProfile) := by
  have first := zero_nash.isSaddlePoint zeroSum
  have second := signs_nash.isSaddlePoint zeroSum
  fin_cases who
  · exact first.value_eq second
  · change expectedUtility payout 1 (form.mixed.play zeroProfile) =
      expectedUtility payout 1 (form.mixed.play signProfile)
    rw [zeroSum.expectedUtility_one, zeroSum.expectedUtility_one, first.value_eq second]

theorem same_zeroSum_values_different_payout_laws :
    IsZeroSum payout ∧
    IsNash form.mixed (euPreference payout) zeroProfile ∧
    IsNash form.mixed (euPreference payout) signProfile ∧
    (∀ who, expectedUtility payout who (form.mixed.play zeroProfile) =
      expectedUtility payout who (form.mixed.play signProfile)) ∧
    payoutLaw zeroProfile ≠ payoutLaw signProfile :=
  ⟨zeroSum, zero_nash, signs_nash, equilibrium_values_equal, payoutLaws_different⟩

end GameTheoryExtensionsTests.ZeroSumOutcomeLaws
