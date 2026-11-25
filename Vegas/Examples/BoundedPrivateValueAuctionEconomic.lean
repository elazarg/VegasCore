module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.BoundedPrivateValueAuction

@[expose] public section

/-! # Truthful finite second-price payoffs -/

noncomputable section

namespace Vegas.Examples.BoundedPrivateValueAuction

open SourceProgram GameTheory GameTheory.Math.Probability
open CommitRevealAuction (Player)

def successfulOutcome (alice bob : Bid) : PublicOutcome program :=
  ⟨Env.cons (.success bob) (Env.cons (.success alice) (Env.empty simpleExpr.Val)),
    ⟨[none, none, none, none]⟩⟩

theorem finalConfig_public (types : Player → Bid) (alice bob : Bid) :
    publicOutcome program (finalConfig types alice bob) = successfulOutcome alice bob := rfl

def surplus (types : Player → Bid) (alice bob : Bid) : Player → ℝ
  | .alice => if bob.val ≤ alice.val then (types .alice).val - (bob.val : ℝ) else 0
  | .bob => if alice.val < bob.val then (types .bob).val - (alice.val : ℝ) else 0

theorem utility_successful (types : Player → Bid) (alice bob : Bid) (who : Player) :
    utility (types, successfulOutcome alice bob) who = surplus types alice bob who := by
  rw [utility_eq_economic]
  cases who <;>
    simp [CommitRevealAuction.utility, CommitRevealAuction.result, surplus,
      successfulOutcome, BoundedPaymentAuction.integerPublication, Env.get, Env.cons]

theorem truthful_alice_payoff_ge (types : Player → Bid) (alternative other : Bid) :
    surplus types alternative other .alice ≤ surplus types (types .alice) other .alice := by
  simp only [surplus]
  have gain : (if other.val ≤ alternative.val then (types .alice).val - other.val else 0) ≤
      (if other.val ≤ (types .alice).val then (types .alice).val - other.val else 0) := by
    split_ifs <;> omega
  exact_mod_cast gain

theorem truthful_bob_payoff_ge (types : Player → Bid) (alternative other : Bid) :
    surplus types other alternative .bob ≤ surplus types other (types .bob) .bob := by
  simp only [surplus]
  have gain : (if other.val < alternative.val then (types .bob).val - other.val else 0) ≤
      (if other.val < (types .bob).val then (types .bob).val - other.val else 0) := by
    split_ifs <;> omega
  exact_mod_cast gain

theorem truthful_joint_distribution (prior : PMF (Player → Bid)) :
    ((setup prior).run truthful).map (fun terminal =>
      (terminal, utility ((setup prior).parameterOutcome values terminal))) =
      prior.map (fun types =>
        (finalConfig types (types .alice) (types .bob),
          surplus types (types .alice) (types .bob))) := by
  rw [truthful_source_distribution, PMF.map_comp]
  apply map_congr_on_support _
  intro types _
  dsimp only [Function.comp_def]
  congr 1
  have retained : initialState program (finalConfig types (types .alice) (types .bob)).state =
      initial types := rfl
  change utility (values (initialState program _), publicOutcome program _) = _
  rw [retained, values_initial, finalConfig_public]
  funext who
  exact utility_successful types _ _ who

private def valuationPair : (Fin 7 × Fin 7) ≃ (Player → Bid) where
  toFun pair who := match who with
    | .alice => BoundedPaymentAuction.bid pair.1
    | .bob => BoundedPaymentAuction.bid pair.2
  invFun types :=
    (⟨(types .alice).val.toNat, by
      have bounds := (types .alice).property
      change (0 : Int) ≤ (types .alice).val ∧ (types .alice).val ≤ 6 at bounds
      omega⟩,
      ⟨(types .bob).val.toNat, by
        have bounds := (types .bob).property
        change (0 : Int) ≤ (types .bob).val ∧ (types .bob).val ≤ 6 at bounds
        omega⟩)
  left_inv pair := by
    apply Prod.ext <;> apply Fin.ext <;> simp [BoundedPaymentAuction.bid]
  right_inv types := by
    funext who
    cases who <;> apply Subtype.ext <;> dsimp [BoundedPaymentAuction.bid]
    · have bounds := (types .alice).property
      change (0 : Int) ≤ (types .alice).val ∧ (types .alice).val ≤ 6 at bounds
      omega
    · have bounds := (types .bob).property
      change (0 : Int) ≤ (types .bob).val ∧ (types .bob).val ≤ 6 at bounds
      omega

private theorem uniformPrior_expected_surplus (who : Player) :
    expect uniformPrior (fun types => surplus types (types .alice) (types .bob) who) = 8 / 7 := by
  have cardinal : Fintype.card (Player → Bid) = 49 := by
    rw [← Fintype.card_congr valuationPair, Fintype.card_prod]
    decide
  rw [expect_eq_sum]
  simp only [uniformPrior, uniformLaw_apply, cardinal]
  rw [← valuationPair.sum_comp]
  cases who <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, valuationPair, surplus,
      BoundedPaymentAuction.bid]

theorem truthful_joint_distribution_expected (who : Player) :
    expect (uniformPrior.map (fun types =>
      (finalConfig types (types .alice) (types .bob),
        surplus types (types .alice) (types .bob)))) (fun realized => realized.2 who) = 8 / 7 := by
  rw [expect_map]
  exact uniformPrior_expected_surplus who


end Vegas.Examples.BoundedPrivateValueAuction
