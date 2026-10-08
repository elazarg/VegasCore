/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.PenaltyPreservation

/-! # Preservation using each sender type's protected payoff

Labels A and B receive at least half the reward from every protected reply.
Label C receives no reward after failure and at most half after success.
These type-specific bounds sharpen the sufficient failure costs without
requiring secrecy for pending late openings.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : LateLeakParameters} {late : Bool}

private theorem convex_lt {p a b upper : ℝ} (p0 : 0 ≤ p) (p1 : p ≤ 1)
    (aUpper : a < upper) (bUpper : b < upper) : p * a + (1 - p) * b < upper := by
  have bound : p * a + (1 - p) * b ≤ max a b := by
    nlinarith [mul_le_mul_of_nonneg_left (le_max_left a b) p0,
      mul_le_mul_of_nonneg_left (le_max_right a b) (sub_nonneg.mpr p1)]
  exact bound.trans_lt (max_lt aUpper bUpper)

theorem lateLeak_sender_success_ge_half (reward : 0 ≤ G.reward)
    (profile : LateLeakProfile G late) (secret : LateLeakType)
    (label : secret.2 ≠ .c) (resolution : LateLeakResolution)
    (success : resolution.succeeded = true) :
    G.reward / 2 ≤
      lateLeakAnswerValue profile (lateLeakStatePayoff G .sender) secret resolution := by
  rw [lateLeak_sender_success_value profile secret resolution success]
  simp only [lateLeakGuessGain, label, ite_false]
  have m1 := lateLeakSafeProb_le_one profile (lateLeakSignal secret resolution)
  nlinarith [mul_nonneg (sub_nonneg.mpr m1) reward]

theorem lateLeak_sender_success_c_le_half (reward : 0 ≤ G.reward)
    (profile : LateLeakProfile G late) (secret : LateLeakType)
    (label : secret.2 = .c) (resolution : LateLeakResolution)
    (success : resolution.succeeded = true) :
    lateLeakAnswerValue profile (lateLeakStatePayoff G .sender) secret resolution ≤
      G.reward / 2 := by
  rw [lateLeak_sender_success_value profile secret resolution success]
  simp only [lateLeakGuessGain, label, ite_true, mul_zero, add_zero]
  have m1 := lateLeakSafeProb_le_one profile (lateLeakSignal secret resolution)
  nlinarith [mul_nonneg (sub_nonneg.mpr m1) reward]

theorem lateLeak_sender_failure_c (profile : LateLeakProfile G late)
    (secret : LateLeakType) (label : secret.2 = .c) (resolution : LateLeakResolution)
    (failure : resolution.succeeded = false) :
    lateLeakAnswerValue profile (lateLeakStatePayoff G .sender) secret resolution =
      -G.forfeit - (if resolution.droppedLate then G.dropCharge else 0) := by
  rw [lateLeak_sender_failure_value profile secret resolution failure]
  simp [lateLeakBitOneGain, lateLeakBitZeroGain, label]

theorem lateLeak_sender_late_send_c_le (reward : 0 ≤ G.reward)
    (profile : LateLeakProfile G late) (secret : LateLeakType) (label : secret.2 = .c)
    (included dropped : LateLeakResolution)
    (success : included.succeeded = true) (failure : dropped.succeeded = false)
    (charged : dropped.droppedLate = true) :
    lateLeakSendValue profile (lateLeakStatePayoff G .sender) secret included dropped ≤
      lateLeakInclusionProb G * (G.reward / 2) -
        (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge) := by
  have upper := lateLeak_sender_success_c_le_half reward profile secret label included success
  have value := lateLeak_sender_failure_c profile secret label dropped failure
  rw [charged] at value
  simp only [ite_true] at value
  unfold lateLeakSendValue
  rw [value]
  nlinarith [mul_le_mul_of_nonneg_left upper (lateLeakInclusionProb_pos G).le]

theorem lateLeak_sender_deferral_c_negative (reward : 0 ≤ G.reward)
    (never : G.reward / 2 < G.forfeit)
    (attempt : G.reward / 2 <
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))
    (profile : LateLeakProfile G late) (secret : LateLeakType) (label : secret.2 = .c) :
    lateLeakFirstValue profile (lateLeakStatePayoff G .sender) secret < 0 := by
  have lateBound : lateLeakInclusionProb G * (G.reward / 2) -
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge) < 0 := by
    have q1 := (lateLeakInclusionProb_lt_one G).le
    nlinarith [mul_nonneg (sub_nonneg.mpr q1) reward]
  have first := (lateLeak_sender_late_send_c_le reward profile secret label
    .firstIncluded .firstDropped rfl rfl rfl).trans_lt lateBound
  have second := (lateLeak_sender_late_send_c_le reward profile secret label
    .secondIncluded .secondDropped rfl rfl rfl).trans_lt lateBound
  have withheld := lateLeak_sender_failure_c profile secret label .withheld rfl
  simp only [LateLeakResolution.droppedLate, Bool.false_eq_true, ite_false, sub_zero] at withheld
  have withheldBound : lateLeakAnswerValue profile (lateLeakStatePayoff G .sender)
      secret .withheld < 0 := by rw [withheld]; linarith
  have secondBound : lateLeakSecondValue profile (lateLeakStatePayoff G .sender) secret < 0 := by
    unfold lateLeakSecondValue
    exact convex_lt (lateLeakOpenProb_nonneg profile (.secondLate secret))
      (lateLeakOpenProb_le_one profile (.secondLate secret)) second withheldBound
  unfold lateLeakFirstValue
  exact convex_lt (lateLeakOpenProb_nonneg profile (.firstLate secret))
    (lateLeakOpenProb_le_one profile (.firstLate secret)) first secondBound

/-- Type-specific failure bounds strictly favor protected opening for every sender. -/
theorem lateLeak_rational_protected_opens_of_half_reward (reward : 0 ≤ G.reward)
    (never : G.reward / 2 < G.forfeit)
    (attempt : G.reward / 2 <
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (secret : LateLeakType) : lateLeakOpenProb A.strategy (.protectedTurn secret) = 1 := by
  let deviation := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) true
    (lateLeak_sender_open_allowed true (.protectedTurn secret) rfl)
  have optimal := lateLeak_sender_rational rational
    (lateLeakSenderSite G true (lateLeakTypeHistory G true secret) rfl)
    (state := .protectedTurn secret) rfl deviation
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn,
    lateLeakValue_protectedTurn, lateLeakProtectedValue, lateLeakProtectedValue,
    lateLeakOpenProb_update_commit_self] at optimal
  simp only [ite_true, one_mul, sub_self, zero_mul, add_zero,
    lateLeakAnswerValue_update_sender] at optimal
  have gap : 0 <
      lateLeakAnswerValue A.strategy (lateLeakStatePayoff G .sender) secret .protectedOpen -
      lateLeakFirstValue A.strategy (lateLeakStatePayoff G .sender) secret := by
    by_cases label : secret.2 = .c
    · have positive := lateLeak_sender_success_nonnegative reward A.strategy secret
        .protectedOpen rfl
      have negative := lateLeak_sender_deferral_c_negative reward never attempt
        A.strategy secret label
      linarith
    · have protectedValue := lateLeak_sender_success_ge_half reward A.strategy secret label
        .protectedOpen rfl
      have deferred := lateLeak_sender_deferral_lt (bound := G.reward / 2) reward
        (by linarith) (by linarith) A.strategy secret
      linarith
  have product : (1 - lateLeakOpenProb A.strategy (.protectedTurn secret)) *
      (lateLeakAnswerValue A.strategy (lateLeakStatePayoff G .sender) secret .protectedOpen -
        lateLeakFirstValue A.strategy (lateLeakStatePayoff G .sender) secret) ≤ 0 := by
    nlinarith [optimal]
  rcases lt_or_eq_of_le (lateLeakOpenProb_le_one A.strategy (.protectedTurn secret))
      with lower | equal
  · have strict := mul_pos (sub_pos.mpr lower) gap
    linarith
  · exact equal

/-- Sequential rationality and on-path Bayes consistency force the intended law
under the type-specific failure bounds, without off-path consistency requirements. -/
theorem lateLeak_outcome_preserved_of_rational_bayes (reward : 0 ≤ G.reward)
    (never : G.reward / 2 < G.forfeit)
    (attempt : G.reward / 2 <
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))
    (A : (lateLeakModel G true).BehavioralAssessment)
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (lateLeakModel G true) A (lateLeak_antichain G true)) :
    lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome := by
  have opens := lateLeak_rational_protected_opens_of_half_reward reward never attempt rational
  exact lateLeak_intended_law_of_protected A.strategy opens
    (lateLeak_rational_bayes_protected_safe rational bayes opens)

/-- Costs above half the reward force the intended law in every sequential equilibrium. -/
theorem lateLeak_outcome_preserved_of_half_reward_costs (reward : 0 ≤ G.reward)
    (never : G.reward / 2 < G.forfeit)
    (attempt : G.reward / 2 <
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))
    (A : (lateLeakModel G true).BehavioralAssessment)
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome := by
  exact lateLeak_outcome_preserved_of_rational_bayes reward never attempt A equilibrium.1
    (equilibrium.2.isBayesConsistent (lateLeak_antichain G true))

/-- The preserving sequential equilibrium exists under the type-specific strict cost bounds. -/
theorem lateLeak_preserving_equilibrium_of_half_reward_costs (reward : 0 ≤ G.reward)
    (never : G.reward / 2 < G.forfeit)
    (attempt : G.reward / 2 <
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge)) :
    ∃ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true)
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome := by
  let fallback : ∀ who, (lateLeakModel G true).Policy who :=
    fun _ _ => Classical.choice inferInstance
  obtain ⟨A, rational, consistent⟩ := (lateLeakModel G true).exists_sequentialEquilibrium
    (lateLeak_decisionRecall G true) fallback (lateLeakPayoff G true) (lateLeak_terminates G true)
  have equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true) := ⟨rational, consistent⟩
  exact ⟨A, equilibrium,
    lateLeak_outcome_preserved_of_half_reward_costs reward never attempt A equilibrium⟩

/-- Every equilibrium of the intended game has a late-turn sequential
equilibrium realizing exactly the same full terminal-state law. -/
theorem lateLeak_sequentialEquilibrium_preserved_of_half_reward_costs
    (reward : 0 ≤ G.reward) (never : G.reward / 2 < G.forfeit)
    (attempt : G.reward / 2 <
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))
    (source : (lateLeakModel G false).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium (lateLeak_antichain G false)
      (lateLeak_terminates G false) (lateLeakPayoff G false)) :
    ∃ target : (lateLeakModel G true).BehavioralAssessment,
      target.IsSequentialEquilibrium (lateLeak_antichain G true)
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      lateLeakOutcomeLaw G true target.strategy = lateLeakOutcomeLaw G false source.strategy := by
  obtain ⟨target, targetEquilibrium, outcome⟩ :=
    lateLeak_preserving_equilibrium_of_half_reward_costs reward never attempt
  exact ⟨target, targetEquilibrium,
    outcome.trans (lateLeak_intended_outcome source equilibrium).symm⟩

/-- A finite charge restores preservation for every fixed inclusion probability below one. -/
theorem lateLeak_preserving_equilibrium_of_half_reward_dropCharge_bound
    (reward : 0 ≤ G.reward) (never : G.reward / 2 < G.forfeit)
    (charge : (G.reward / 2) / (1 - lateLeakInclusionProb G) ≤ G.dropCharge) :
    ∃ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true)
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome := by
  have delta : 0 < 1 - lateLeakInclusionProb G := sub_pos.mpr (lateLeakInclusionProb_lt_one G)
  have collected : G.reward / 2 ≤ (1 - lateLeakInclusionProb G) * G.dropCharge := by
    have bound := (div_le_iff₀ delta).mp charge
    nlinarith [bound]
  apply lateLeak_preserving_equilibrium_of_half_reward_costs reward never
  have positive : 0 < G.forfeit := by linarith
  nlinarith [mul_pos delta positive]

theorem lateLeak_exists_preserving_dropCharge_of_half_reward (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (never : G.reward / 2 < G.forfeit) :
    ∃ charge : ℝ, 0 ≤ charge ∧
      ∃ A : (lateLeakModel { G with dropCharge := charge } true).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain { G with dropCharge := charge } true)
          (lateLeak_terminates { G with dropCharge := charge } true)
          (lateLeakPayoff { G with dropCharge := charge } true) ∧
        lateLeakOutcomeLaw { G with dropCharge := charge } true A.strategy =
          lateLeakIntendedOutcome := by
  refine ⟨(G.reward / 2) / (1 - lateLeakInclusionProb G), div_nonneg (by linarith)
    (sub_pos.mpr (lateLeakInclusionProb_lt_one G)).le, ?_⟩
  exact lateLeak_preserving_equilibrium_of_half_reward_dropCharge_bound
    reward never (le_refl _)

/-- A finite failure forfeit alone restores preservation at any fixed
inclusion probability below one; no charge on dropped packets is necessary. -/
theorem lateLeak_exists_preserving_forfeit_without_dropCharge (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) :
    ∃ forfeit : ℝ, 0 ≤ forfeit ∧
      ∃ A :
          (lateLeakModel { G with forfeit := forfeit, dropCharge := 0 } true).BehavioralAssessment,
        A.IsSequentialEquilibrium
          (lateLeak_antichain { G with forfeit := forfeit, dropCharge := 0 } true)
          (lateLeak_terminates { G with forfeit := forfeit, dropCharge := 0 } true)
          (lateLeakPayoff { G with forfeit := forfeit, dropCharge := 0 } true) ∧
        lateLeakOutcomeLaw { G with forfeit := forfeit, dropCharge := 0 } true A.strategy =
          lateLeakIntendedOutcome := by
  let delta := 1 - lateLeakInclusionProb G
  have delta_pos : 0 < delta := sub_pos.mpr (lateLeakInclusionProb_lt_one G)
  have delta_le_one : delta ≤ 1 := by
    dsimp [delta]
    linarith [lateLeakInclusionProb_pos G]
  have divided : G.reward / 2 ≤ (G.reward / 2) / delta := by
    apply (le_div_iff₀ delta_pos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr delta_le_one) reward]
  let forfeit := (G.reward / 2) / delta + 1
  have scaled : delta * forfeit = G.reward / 2 + delta := by
    dsimp [forfeit]
    rw [mul_add, mul_one, mul_comm delta ((G.reward / 2) / delta),
      div_mul_cancel₀ _ delta_pos.ne']
  refine ⟨forfeit, ?_, ?_⟩
  · dsimp [forfeit]
    linarith
  · apply lateLeak_preserving_equilibrium_of_half_reward_costs
    · exact reward
    · change G.reward / 2 < forfeit
      dsimp [forfeit]
      linarith
    · change G.reward / 2 < delta * (forfeit + 0)
      rw [add_zero, scaled]
      linarith

end Vegas
