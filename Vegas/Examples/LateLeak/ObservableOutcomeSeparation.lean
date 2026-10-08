/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.OutcomeSeparation

/-! # Outcome separation after erasing transmission timing

The joint readout retains the initial type, successful versus failed
resolution, and the listener's answer. It forgets which transmission turn
produced a successful opening.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : LateLeakParameters} {late : Bool}

/-- Initial parameters and the terminal result, with transmission timing
erased. Nonterminal states have no result. -/
def lateLeakResultReadout : LateLeakState → Option (LateLeakType × Bool × LateLeakAnswer)
  | .finished secret resolution answer => some (secret, resolution.succeeded, answer)
  | _ => none

/-- The joint outcome law after forgetting transmission timing. -/
def lateLeakResultLaw (G : LateLeakParameters) (late : Bool)
    (profile : LateLeakProfile G late) : PMF (Option (LateLeakType × Bool × LateLeakAnswer)) :=
  (lateLeakOutcomeLaw G late profile).map lateLeakResultReadout

/-- The intended joint result law after forgetting transmission timing. -/
def lateLeakIntendedResultLaw : PMF (Option (LateLeakType × Bool × LateLeakAnswer)) :=
  lateLeakIntendedOutcome.map lateLeakResultReadout

/-- The intended result is successful safe play for every initial type. -/
theorem lateLeakIntendedResultLaw_apply (secret : LateLeakType) :
    lateLeakIntendedResultLaw (some (secret, true, .safe)) = lateLeakPrior secret := by
  rw [lateLeakIntendedResultLaw, lateLeakIntendedOutcome, PMF.map_comp]
  change (lateLeakPrior.map (fun other => some (other, true, LateLeakAnswer.safe))) _ = _
  exact pmf_map_apply_of_injective lateLeakPrior
    (fun _ _ same => (Option.some.inj same |> Prod.mk.inj).1) secret

/-- Successful safe mass consists of the protected branch and the possible
late successful branches. -/
theorem lateLeakResultLaw_success_safe (profile : LateLeakProfile G late)
    (secret : LateLeakType) :
    (lateLeakResultLaw G late profile (some (secret, true, .safe))).toReal =
      (lateLeakPrior secret).toReal *
        (lateLeakOpenProb profile (.protectedTurn secret) *
            lateLeakSafeProb profile (.protectedSuccess secret.1) +
          (1 - lateLeakOpenProb profile (.protectedTurn secret)) *
            (lateLeakOpenProb profile (.firstLate secret) * lateLeakInclusionProb G *
                lateLeakSafeProb profile (.firstSuccess secret.1) +
              (1 - lateLeakOpenProb profile (.firstLate secret)) *
                (lateLeakOpenProb profile (.secondLate secret) * lateLeakInclusionProb G *
                  lateLeakSafeProb profile (.secondSuccess secret.1)))) := by
  let indicator : LateLeakState → ℝ := fun state =>
    if some (secret, true, LateLeakAnswer.safe) = lateLeakResultReadout state then 1 else 0
  have read : (lateLeakResultLaw G late profile (some (secret, true, .safe))).toReal =
      lateLeakValue profile indicator (0 + 5) .initial := by
    rw [lateLeakResultLaw, toReal_map_apply, lateLeakValue, ← lateLeakOutcomeLaw_eq]
    apply expect_congr_on_support
    intro state _
    dsimp [indicator]
    split_ifs <;> rfl
  have answer (other : LateLeakType) (resolution : LateLeakResolution) :
      lateLeakAnswerValue profile indicator other resolution =
        if other = secret ∧ resolution.succeeded = true then
          lateLeakSafeProb profile (lateLeakSignal other resolution) else 0 := by
    rw [lateLeakAnswerValue, lateLeak_expect_two_point _ (some (.reply .safe)) _ 0]
    · simp only [indicator, lateLeakResultReadout, lateLeakReplyOf, Option.some.injEq,
        Prod.mk.injEq, and_true, mul_zero, add_zero]
      by_cases hit : other = secret ∧ resolution.succeeded = true
      · obtain ⟨rfl, succeeded⟩ := hit
        simp [succeeded, lateLeakSafeProb]
      · have missing : ¬(secret = other ∧ resolution.succeeded = true) := by
          intro same
          exact hit ⟨same.1.symm, same.2⟩
        simp [hit, missing]
    · intro choice supported different
      obtain ⟨answer, rfl, -⟩ := lateLeakReplyLaw_support profile _ choice supported
      have not_safe : answer ≠ .safe := fun same => different (by rw [same])
      simp [indicator, lateLeakResultReadout, lateLeakReplyOf, Ne.symm not_safe]
  have protectedValue (other : LateLeakType) :
      lateLeakProtectedValue profile indicator other =
        if secret = other then
          lateLeakOpenProb profile (.protectedTurn secret) *
              lateLeakSafeProb profile (.protectedSuccess secret.1) +
            (1 - lateLeakOpenProb profile (.protectedTurn secret)) *
              (lateLeakOpenProb profile (.firstLate secret) * lateLeakInclusionProb G *
                  lateLeakSafeProb profile (.firstSuccess secret.1) +
                (1 - lateLeakOpenProb profile (.firstLate secret)) *
                  (lateLeakOpenProb profile (.secondLate secret) * lateLeakInclusionProb G *
                    lateLeakSafeProb profile (.secondSuccess secret.1))) else 0 := by
    simp only [lateLeakProtectedValue, lateLeakFirstValue, lateLeakSecondValue,
      lateLeakSendValue, answer]
    by_cases same : secret = other
    · subst same
      simp only [LateLeakResolution.succeeded, lateLeakSignal, Bool.false_eq_true,
        and_self, and_false, ite_false, ite_true, mul_zero, add_zero]
      ring
    · simp [same, Ne.symm same]
  rw [read, lateLeakValue_initial]
  simp only [protectedValue]
  rw [expect_ite_eq]

private theorem late_safe_probability_le (profile : LateLeakProfile G late)
    (secret : LateLeakType) :
    lateLeakOpenProb profile (.firstLate secret) * lateLeakInclusionProb G *
          lateLeakSafeProb profile (.firstSuccess secret.1) +
        (1 - lateLeakOpenProb profile (.firstLate secret)) *
          (lateLeakOpenProb profile (.secondLate secret) * lateLeakInclusionProb G *
            lateLeakSafeProb profile (.secondSuccess secret.1)) ≤
      lateLeakInclusionProb G := by
  have q_nonnegative := (lateLeakInclusionProb_pos G).le
  have first_le := mul_le_mul_of_nonneg_left
    (lateLeakSafeProb_le_one profile (.firstSuccess secret.1))
    (mul_nonneg (lateLeakOpenProb_nonneg profile (.firstLate secret)) q_nonnegative)
  have second_le : lateLeakOpenProb profile (.secondLate secret) *
      lateLeakInclusionProb G * lateLeakSafeProb profile (.secondSuccess secret.1) ≤
      lateLeakInclusionProb G := by
    have small := mul_le_mul_of_nonneg_left
      (lateLeakSafeProb_le_one profile (.secondSuccess secret.1))
      (mul_nonneg (lateLeakOpenProb_nonneg profile (.secondLate secret)) q_nonnegative)
    have bounded := mul_le_mul_of_nonneg_right
      (lateLeakOpenProb_le_one profile (.secondLate secret)) q_nonnegative
    nlinarith
  have weighted_second := mul_le_mul_of_nonneg_left second_le
    (sub_nonneg.mpr (lateLeakOpenProb_le_one profile (.firstLate secret)))
  nlinarith

/-- A sequential equilibrium loses successful-safe result mass even after
the transmission turn has been erased. -/
theorem lateLeak_equilibrium_result_mass_gap (pays : G.DeferralPays)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    ∃ bit, (3 / 20 : ℝ) *
        (G.reward - max
          (2 * (G.reward - (lateLeakInclusionProb G * G.reward -
            (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))))
          (lateLeakInclusionProb G * G.reward)) ≤
      G.reward *
        ((lateLeakIntendedResultLaw (some ((bit, .a), true, .safe))).toReal -
          (lateLeakResultLaw G true A.strategy (some ((bit, .a), true, .safe))).toReal) := by
  obtain ⟨bit, guessing⟩ := lateLeak_equilibrium_late_guess pays equilibrium
  refine ⟨bit, ?_⟩
  let cap := max
    (2 * (G.reward - (lateLeakInclusionProb G * G.reward -
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))))
    (lateLeakInclusionProb G * G.reward)
  have protected_le : lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)) *
      lateLeakSafeProb A.strategy (.protectedSuccess bit) * G.reward ≤
      lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)) * cap := by
    by_cases zero : lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)) = 0
    · simp [zero]
    · have positive : 0 < lateLeakOpenProb A.strategy (.protectedTurn (bit, .a)) :=
        lt_of_le_of_ne (lateLeakOpenProb_nonneg A.strategy _) (Ne.symm zero)
      have safe_le := lateLeak_protected_safe_bound_of_late_guess pays.reward_pos
        equilibrium.1 bit positive guessing
      have bounded := mul_le_mul_of_nonneg_left
        (safe_le.trans (le_max_left _ (lateLeakInclusionProb G * G.reward)))
        (lateLeakOpenProb_nonneg A.strategy (.protectedTurn (bit, .a)))
      dsimp [cap]
      nlinarith
  have late_le := mul_le_mul_of_nonneg_right
    (late_safe_probability_le A.strategy (bit, .a)) pays.reward_pos.le
  have late_cap := late_le.trans (le_max_right
    (2 * (G.reward - (lateLeakInclusionProb G * G.reward -
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))))
    (lateLeakInclusionProb G * G.reward))
  have weighted_late := mul_le_mul_of_nonneg_left late_cap
    (sub_nonneg.mpr (lateLeakOpenProb_le_one A.strategy (.protectedTurn (bit, .a))))
  have prior_nonnegative : 0 ≤ (lateLeakPrior (bit, .a)).toReal := ENNReal.toReal_nonneg
  have prior_lower : (3 / 20 : ℝ) ≤ (lateLeakPrior (bit, .a)).toReal := by
    cases bit <;> norm_num [lateLeakPrior, PMF.ofFintype_apply]
  have gap_nonnegative : 0 ≤ G.reward - cap := by
    apply sub_nonneg.mpr
    apply max_le
    · linarith [pays.guess_beats_safe]
    · have := mul_le_mul_of_nonneg_right
        (lateLeakInclusionProb_lt_one G).le pays.reward_pos.le
      simpa using this
  have weighted_gap := mul_le_mul_of_nonneg_right prior_lower gap_nonnegative
  have first_weighted := mul_le_mul_of_nonneg_left protected_le prior_nonnegative
  have late_weighted := mul_le_mul_of_nonneg_left weighted_late prior_nonnegative
  rw [lateLeakIntendedResultLaw_apply, lateLeakResultLaw_success_safe]
  dsimp [cap] at first_weighted weighted_gap ⊢
  nlinarith

/-- Total variation remains bounded away from zero after transmission timing
is erased from the result. -/
theorem lateLeak_equilibrium_result_totalVariation_lower_bound (pays : G.DeferralPays)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true))
    {error : ℝ}
    (close : PMF.WithinTV error (lateLeakResultLaw G true A.strategy)
      lateLeakIntendedResultLaw) :
    (3 / 20 : ℝ) *
        (G.reward - max
          (2 * (G.reward - (lateLeakInclusionProb G * G.reward -
            (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))))
          (lateLeakInclusionProb G * G.reward)) ≤
      G.reward * error := by
  obtain ⟨bit, gap⟩ := lateLeak_equilibrium_result_mass_gap pays equilibrium
  have atom := close.symm.apply (some ((bit, .a), true, .safe))
  have difference := (le_abs_self _).trans atom
  exact gap.trans (mul_le_mul_of_nonneg_left difference pays.reward_pos.le)

/-- No sequential equilibrium preserves the intended joint law of initial
parameters, success and answer, even without transmission timing. -/
theorem lateLeak_equilibrium_result_not_preserved (pays : G.DeferralPays)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    lateLeakResultLaw G true A.strategy ≠ lateLeakIntendedResultLaw := by
  intro same
  have close : PMF.WithinTV 0 (lateLeakResultLaw G true A.strategy)
      lateLeakIntendedResultLaw := by rw [same]; exact PMF.WithinTV.refl _
  have bound := lateLeak_equilibrium_result_totalVariation_lower_bound pays equilibrium close
  have cap_lt : max
      (2 * (G.reward - (lateLeakInclusionProb G * G.reward -
        (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))))
      (lateLeakInclusionProb G * G.reward) < G.reward := by
    apply max_lt_iff.mpr
    constructor
    · linarith [pays.guess_beats_safe]
    · have := mul_lt_mul_of_pos_right (lateLeakInclusionProb_lt_one G) pays.reward_pos
      simpa using this
  nlinarith

/-- At the sample parameters every sequential equilibrium loses at least
3/2000 of some intended successful-safe result atom after timing is erased. -/
theorem lateLeak_sample_result_mass_gap
    {A : (lateLeakModel LateLeakParameters.sample true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain LateLeakParameters.sample true)
      (lateLeak_terminates LateLeakParameters.sample true)
      (lateLeakPayoff LateLeakParameters.sample true)) :
    ∃ bit, (3 / 2000 : ℝ) ≤
      (lateLeakIntendedResultLaw (some ((bit, .a), true, .safe))).toReal -
        (lateLeakResultLaw LateLeakParameters.sample true A.strategy
          (some ((bit, .a), true, .safe))).toReal := by
  obtain ⟨bit, bound⟩ :=
    lateLeak_equilibrium_result_mass_gap LateLeakParameters.sample_deferralPays equilibrium
  refine ⟨bit, ?_⟩
  norm_num [LateLeakParameters.sample, lateLeakInclusionProb] at bound
  linarith

/-- No sample sequential-equilibrium result law is closer than 3/2000 in
total variation to the intended result law after timing is erased. -/
theorem lateLeak_sample_result_totalVariation_lower_bound
    {A : (lateLeakModel LateLeakParameters.sample true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain LateLeakParameters.sample true)
      (lateLeak_terminates LateLeakParameters.sample true)
      (lateLeakPayoff LateLeakParameters.sample true))
    {error : ℝ}
    (close : PMF.WithinTV error
      (lateLeakResultLaw LateLeakParameters.sample true A.strategy)
      lateLeakIntendedResultLaw) :
    (3 / 2000 : ℝ) ≤ error := by
  obtain ⟨bit, gap⟩ := lateLeak_sample_result_mass_gap equilibrium
  exact gap.trans ((le_abs_self _).trans (close.symm.apply (some ((bit, .a), true, .safe))))

end Vegas
