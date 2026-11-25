module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensSetup
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

open GameTheory.Math.Probability

/-! # Odd's commitment payoff with possible failure of Even's publication -/

noncomputable section

namespace Vegas.Examples.OddsEvens

/-- Odd makes a successful opening against a supplied distribution of Even's publication. -/
def oddCommitmentPayoff (opponent : PMF (PublicationResult Bool)) (bit : Bool) : ℝ :=
  expect opponent fun result => (cash result (.success bit) odd : ℝ)

/-- Failure pays the survivor equally for either bit. The payoff difference
depends on the unconditional masses of the two successful publications. -/
theorem oddCommitmentPayoff_difference (opponent : PMF (PublicationResult Bool)) :
    oddCommitmentPayoff opponent false - oddCommitmentPayoff opponent true =
      52 * ((opponent (.success true)).toReal - (opponent (.success false)).toReal) := by
  have outcomes : (Finset.univ : Finset (PublicationResult Bool)) =
      {.failure, .success false, .success true} := by decide
  simp only [oddCommitmentPayoff, expect_eq_sum, outcomes]
  norm_num [cash, even, odd]
  ring

/-- A fair coin maximizes base payoff among all randomized successful choices
exactly when both successful opposing values have equal probability. The
opponent's publication distribution is fixed across these choices. -/
theorem fairCommitment_optimal_iff (opponent : PMF (PublicationResult Bool)) :
    (∀ replacement : PMF Bool, expect replacement (oddCommitmentPayoff opponent) ≤
      expect (uniformLaw Bool) (oddCommitmentPayoff opponent)) ↔
      (opponent (.success true)).toReal = (opponent (.success false)).toReal := by
  have difference := oddCommitmentPayoff_difference opponent
  constructor
  · intro best
    have left := best (PMF.pure false)
    have right := best (PMF.pure true)
    rw [expect_pure, expect_eq_sum, Fintype.sum_bool] at left right
    norm_num [uniformLaw_apply] at left right
    linarith
  · intro equal replacement
    have same : oddCommitmentPayoff opponent true = oddCommitmentPayoff opponent false := by
      linarith
    have constant : oddCommitmentPayoff opponent = fun _ => oddCommitmentPayoff opponent false := by
      funext bit
      cases bit <;> simp [same]
    rw [constant, expect_constant, expect_constant]

end Vegas.Examples.OddsEvens
