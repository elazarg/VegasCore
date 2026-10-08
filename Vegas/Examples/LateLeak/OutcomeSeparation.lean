/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Preservation
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Quantitative outcome separation for late sends

Consistent late-turn incentives force some protected success to lose a
positive amount of its intended safe-answer mass. The estimate applies to
every sequential equilibrium, rather than only profiles preserving the
intended outcome.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : LateLeakParameters}

/-- If a sender type uses its protected opening with positive probability,
its protected continuation dominates every whole-policy deviation. -/
theorem lateLeak_protected_support_value
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (secret : LateLeakType)
    (positive : 0 < lateLeakOpenProb A.strategy (.protectedTurn secret))
    (alternative : (lateLeakModel G true).BehavioralPolicy .sender) :
    lateLeakValue (lateLeakUpdate A.strategy .sender alternative)
        (lateLeakStatePayoff G .sender) 5 (.protectedTurn secret) ≤
      lateLeakAnswerValue A.strategy (lateLeakStatePayoff G .sender) secret .protectedOpen := by
  let wait := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) false
    ⟨false, rfl, rfl⟩
  have waiting := lateLeak_sender_rational rational
    (lateLeakSenderSite G true (lateLeakTypeHistory G true secret) rfl)
    (state := .protectedTurn secret) rfl wait
  have optimal := lateLeak_sender_rational rational
    (lateLeakSenderSite G true (lateLeakTypeHistory G true secret) rfl)
    (state := .protectedTurn secret) rfl alternative
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn,
    lateLeakValue_protectedTurn, lateLeakProtectedValue, lateLeakProtectedValue] at waiting
  have first_eq : lateLeakFirstValue (lateLeakUpdate A.strategy .sender wait)
      (lateLeakStatePayoff G .sender) secret =
      lateLeakFirstValue A.strategy (lateLeakStatePayoff G .sender) secret := by
    dsimp [lateLeakFirstValue, lateLeakSecondValue, wait]
    rw [lateLeakOpenProb_update_commit_of_ne A.strategy (A.strategy .sender)
        (.protectedTurn secret) (.firstLate secret) false _ (by simp),
      lateLeakOpenProb_update_commit_of_ne A.strategy (A.strategy .sender)
        (.protectedTurn secret) (.secondLate secret) false _ (by simp)]
    simp only [lateLeakUpdate_self, lateLeakSendValue_update_sender,
      lateLeakAnswerValue_update_sender]
  rw [first_eq] at waiting
  simp only [wait, lateLeakOpenProb_update_commit_self,
    lateLeakAnswerValue_update_sender, Bool.false_eq_true, ite_false, zero_mul,
    sub_zero, one_mul, zero_add] at waiting
  have first_le : lateLeakFirstValue A.strategy (lateLeakStatePayoff G .sender) secret ≤
      lateLeakAnswerValue A.strategy (lateLeakStatePayoff G .sender) secret .protectedOpen := by
    have product : 0 ≤ lateLeakOpenProb A.strategy (.protectedTurn secret) *
        (lateLeakAnswerValue A.strategy (lateLeakStatePayoff G .sender) secret .protectedOpen -
          lateLeakFirstValue A.strategy (lateLeakStatePayoff G .sender) secret) := by
      nlinarith [waiting]
    have := (mul_nonneg_iff_of_pos_left positive).mp product
    linarith
  have p_le := lateLeakOpenProb_le_one A.strategy (.protectedTurn secret)
  have comparison := mul_le_mul_of_nonneg_left first_le (sub_nonneg.mpr p_le)
  calc
    _ ≤ lateLeakValue A.strategy (lateLeakStatePayoff G .sender) 5
        (.protectedTurn secret) := optimal
    _ = lateLeakProtectedValue A.strategy (lateLeakStatePayoff G .sender) secret :=
      lateLeakValue_protectedTurn _ _ 1 _
    _ ≤ _ := by dsimp [lateLeakProtectedValue]; nlinarith

/-- Some late success induces a guess in every sequential equilibrium. -/
theorem lateLeak_equilibrium_late_guess (pays : G.DeferralPays)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    ∃ bit, lateLeakSafeProb A.strategy (.firstSuccess bit) = 0 ∨
      lateLeakSafeProb A.strategy (.secondSuccess bit) = 0 := by
  obtain ⟨rational, consistent⟩ := equilibrium
  obtain ⟨bit, sender, holder, senderPrefers, holderPrefers⟩ :=
    lateLeak_opposite_preferences pays.reward_pos rational
  have sends := (lateLeak_rational_first_turn pays rational (bit, sender)).1 senderPrefers
  have holds := (lateLeak_rational_first_turn pays rational (bit, holder)).2 holderPrefers
  have holderSends := lateLeak_rational_second_sends pays rational (bit, holder)
  refine ⟨bit, ?_⟩
  rcases lateLeak_consistent_face consistent bit sender holder sends holds holderSends with
    zero | zero
  · have reward := lateLeak_guess_reward_zero A (lateLeakFirstSuccessSite G bit)
      (.firstSuccess bit) rfl rfl _ (bit, holder) .firstIncluded rfl zero
    exact Or.inl (lateLeak_rational_guesses rational _ _ rfl rfl _ reward)
  · have reward := lateLeak_guess_reward_zero A (lateLeakSecondSuccessSite G bit)
      (.secondSuccess bit) rfl rfl _ (bit, sender) .secondIncluded rfl zero
    exact Or.inr (lateLeak_rational_guesses rational _ _ rfl rfl _ reward)

private theorem protected_safe_bound_first (reward_pos : 0 < G.reward)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (bit : Bool) (positive : 0 < lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)))
    (guessing : lateLeakSafeProb A.strategy (.firstSuccess bit) = 0) :
    lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward ≤
      2 * (G.reward - (lateLeakInclusionProb G * G.reward -
        (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))) := by
  let secret : LateLeakType := (bit, .a)
  let wait := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) false
    ⟨false, rfl, rfl⟩
  let deviation := lateLeakCommitOpen wait (.firstLate secret) true ⟨true, rfl⟩
  have optimal := lateLeak_protected_support_value rational secret positive deviation
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn,
    lateLeakProtectedValue, lateLeakFirstValue,
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_self, lateLeakOpenProb_update_commit_self,
    lateLeakSendValue_update_sender, lateLeak_first_send_value,
    lateLeak_sender_success_value A.strategy secret .protectedOpen rfl] at optimal
  simp only [Bool.false_eq_true, ite_false, ite_true, zero_mul, sub_zero, one_mul,
    zero_add, lateLeakSignal] at optimal
  rw [show secret.1 = bit from rfl, guessing] at optimal
  simp only [secret, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain,
    reduceCtorEq, ite_true, ite_false] at optimal
  have gain_nonnegative := mul_nonneg
    (sub_nonneg.mpr (lateLeakInclusionProb_lt_one G).le)
    (mul_nonneg (lateLeakBitOneProb_nonneg A.strategy (.leakedFailure bit)) reward_pos.le)
  nlinarith

private theorem protected_safe_bound_second (reward_pos : 0 < G.reward)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (bit : Bool) (positive : 0 < lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)))
    (guessing : lateLeakSafeProb A.strategy (.secondSuccess bit) = 0) :
    lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward ≤
      2 * (G.reward - (lateLeakInclusionProb G * G.reward -
        (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))) := by
  let secret : LateLeakType := (bit, .a)
  let wait := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) false
    ⟨false, rfl, rfl⟩
  let hold := lateLeakCommitOpen wait (.firstLate secret) false ⟨false, rfl⟩
  let deviation := lateLeakCommitOpen hold (.secondLate secret) true ⟨true, rfl⟩
  have optimal := lateLeak_protected_support_value rational secret positive deviation
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn,
    lateLeakProtectedValue, lateLeakFirstValue, lateLeakSecondValue,
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_self,
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_self, lateLeakOpenProb_update_commit_self,
    lateLeakSendValue_update_sender, lateLeakSendValue_update_sender, lateLeak_second_send_value,
    lateLeak_sender_success_value A.strategy secret .protectedOpen rfl] at optimal
  simp only [Bool.false_eq_true, ite_false, ite_true, zero_mul, sub_zero, one_mul,
    zero_add, sub_self, add_zero, lateLeakSignal] at optimal
  rw [show secret.1 = bit from rfl, guessing] at optimal
  simp only [secret, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain,
    reduceCtorEq, ite_true, ite_false] at optimal
  have gain_nonnegative := mul_nonneg
    (sub_nonneg.mpr (lateLeakInclusionProb_lt_one G).le)
    (mul_nonneg (lateLeakBitOneProb_nonneg A.strategy .silentFailure) reward_pos.le)
  nlinarith

/-- A positive-probability protected opening must pay at least the reward
available at a late inclusion where the listener guesses. -/
theorem lateLeak_protected_safe_bound_of_late_guess (reward_pos : 0 < G.reward)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (bit : Bool) (positive : 0 < lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)))
    (guessing : lateLeakSafeProb A.strategy (.firstSuccess bit) = 0 ∨
      lateLeakSafeProb A.strategy (.secondSuccess bit) = 0) :
    lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward ≤
      2 * (G.reward - (lateLeakInclusionProb G * G.reward -
        (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))) := by
  rcases guessing with first | second
  · exact protected_safe_bound_first reward_pos rational bit positive first
  · exact protected_safe_bound_second reward_pos rational bit positive second

/-- Every sequential equilibrium loses protected safe mass in some bit class.
The inequality is scaled by the reward to avoid dividing by it. -/
theorem lateLeak_equilibrium_protected_safe_bound (pays : G.DeferralPays)
    (cost_nonnegative : 0 ≤ G.forfeit + G.dropCharge)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    ∃ bit, lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)) *
        lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward ≤
      2 * (G.reward - (lateLeakInclusionProb G * G.reward -
        (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))) := by
  obtain ⟨bit, guessing⟩ := lateLeak_equilibrium_late_guess pays equilibrium
  refine ⟨bit, ?_⟩
  by_cases zero : lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)) = 0
  · rw [zero, zero_mul, zero_mul]
    have loss_nonnegative := mul_nonneg
      (sub_nonneg.mpr (lateLeakInclusionProb_lt_one G).le) cost_nonnegative
    have reward_bound := mul_le_mul_of_nonneg_right
      (lateLeakInclusionProb_lt_one G).le pays.reward_pos.le
    nlinarith
  · have positive : 0 < lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)) :=
      lt_of_le_of_ne (lateLeakOpenProb_nonneg A.strategy _) (Ne.symm zero)
    have safe_bound : lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward ≤
        2 * (G.reward - (lateLeakInclusionProb G * G.reward -
          (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))) := by
      rcases guessing with first | second
      · exact protected_safe_bound_first pays.reward_pos equilibrium.1 bit positive first
      · exact protected_safe_bound_second pays.reward_pos equilibrium.1 bit positive second
    calc
      _ = lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)) *
          (lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward) := by ring
      _ ≤ 1 * (lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward) :=
        mul_le_mul_of_nonneg_right (lateLeakOpenProb_le_one A.strategy _)
          (mul_nonneg (lateLeakSafeProb_nonneg A.strategy _) pays.reward_pos.le)
      _ = lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward := by ring
      _ ≤ _ := safe_bound

/-- A type of label A loses a uniformly positive amount of intended
protected-safe probability in every sequential equilibrium. -/
theorem lateLeak_equilibrium_protected_safe_mass_gap (pays : G.DeferralPays)
    (cost_nonnegative : 0 ≤ G.forfeit + G.dropCharge)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    ∃ bit, (3 / 20 : ℝ) *
        (2 * (lateLeakInclusionProb G * G.reward -
          (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge)) - G.reward) ≤
      G.reward * ((lateLeakIntendedOutcome (.finished (bit, .a) .protectedOpen .safe)).toReal -
        (lateLeakOutcomeLaw G true A.strategy
          (.finished (bit, .a) .protectedOpen .safe)).toReal) := by
  obtain ⟨bit, bound⟩ :=
    lateLeak_equilibrium_protected_safe_bound pays cost_nonnegative equilibrium
  refine ⟨bit, ?_⟩
  rw [lateLeakIntendedOutcome_apply, lateLeakOutcomeLaw_protected_safe]
  have prior_nonnegative : 0 ≤ (lateLeakPrior (bit, .a)).toReal := ENNReal.toReal_nonneg
  have prior_lower : (3 / 20 : ℝ) ≤ (lateLeakPrior (bit, .a)).toReal := by
    cases bit <;> norm_num [lateLeakPrior, PMF.ofFintype_apply]
  have gap_nonnegative : 0 ≤ 2 * (lateLeakInclusionProb G * G.reward -
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge)) - G.reward := by
    linarith [pays.guess_beats_safe]
  have weighted_bound := mul_le_mul_of_nonneg_left bound prior_nonnegative
  have weighted_gap := mul_le_mul_of_nonneg_right prior_lower gap_nonnegative
  nlinarith

/-- At the sample parameters every sequential equilibrium misses at least
267/2000 of some intended protected-safe atom. -/
theorem lateLeak_sample_protected_safe_mass_gap
    {A : (lateLeakModel LateLeakParameters.sample true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain LateLeakParameters.sample true)
      (lateLeak_terminates LateLeakParameters.sample true)
      (lateLeakPayoff LateLeakParameters.sample true)) :
    ∃ bit, (267 / 2000 : ℝ) ≤
      (lateLeakIntendedOutcome (.finished (bit, .a) .protectedOpen .safe)).toReal -
        (lateLeakOutcomeLaw LateLeakParameters.sample true A.strategy
          (.finished (bit, .a) .protectedOpen .safe)).toReal := by
  obtain ⟨bit, bound⟩ := lateLeak_equilibrium_protected_safe_mass_gap
    LateLeakParameters.sample_deferralPays (by norm_num [LateLeakParameters.sample]) equilibrium
  refine ⟨bit, ?_⟩
  norm_num [LateLeakParameters.sample, lateLeakInclusionProb] at bound
  linarith

/-- Any total-variation tolerance covering a sequential-equilibrium outcome
must be at least the protected-safe probability deficit. -/
theorem lateLeak_equilibrium_totalVariation_lower_bound (pays : G.DeferralPays)
    (cost_nonnegative : 0 ≤ G.forfeit + G.dropCharge)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true))
    {error : ℝ}
    (close : PMF.WithinTV error (lateLeakOutcomeLaw G true A.strategy)
      lateLeakIntendedOutcome) :
    (3 / 20 : ℝ) * (2 * (lateLeakInclusionProb G * G.reward -
        (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge)) - G.reward) ≤
      G.reward * error := by
  obtain ⟨bit, gap⟩ :=
    lateLeak_equilibrium_protected_safe_mass_gap pays cost_nonnegative equilibrium
  have atom := close.symm.apply (.finished (bit, .a) .protectedOpen .safe)
  have difference := (le_abs_self _).trans atom
  exact gap.trans (mul_le_mul_of_nonneg_left difference pays.reward_pos.le)

/-- The sample's intended outcome cannot be approximated in total variation
more closely than 267/2000 by any sequential equilibrium. -/
theorem lateLeak_sample_totalVariation_lower_bound
    {A : (lateLeakModel LateLeakParameters.sample true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain LateLeakParameters.sample true)
      (lateLeak_terminates LateLeakParameters.sample true)
      (lateLeakPayoff LateLeakParameters.sample true))
    {error : ℝ}
    (close : PMF.WithinTV error (lateLeakOutcomeLaw LateLeakParameters.sample true A.strategy)
      lateLeakIntendedOutcome) :
    (267 / 2000 : ℝ) ≤ error := by
  obtain ⟨bit, gap⟩ := lateLeak_sample_protected_safe_mass_gap equilibrium
  exact gap.trans ((le_abs_self _).trans
    (close.symm.apply (.finished (bit, .a) .protectedOpen .safe)))

end Vegas
