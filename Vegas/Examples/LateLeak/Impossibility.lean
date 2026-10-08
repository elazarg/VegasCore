/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Consistency

/-! # No sequential equilibrium of the late-turn game has the intended outcome

Suppose a sequential equilibrium of the late-turn game has the intended
outcome: every type opens at the protected turn and the listener answers
safely. Each step uses only part of the hypothesis that deferring pays.

* Every answer after a success acts on the sender along one direction, so the
  sender's late-turn values depend on the listener only through its safe
  probabilities and its bit guesses after failures. This holds for all
  parameters.
* When `q (D - R) > (1 - q) c` and `R ≥ 0`, sending at the second late turn
  strictly beats never sending.
* Whatever the listener answers after an unseen failure, the leak after a
  first-turn failure separates labels `A` and `B` in some class of the
  committed bit, so two types of that class strictly prefer opposite late
  turns, for every choice of the listener's answers after successes. This
  needs `R > 0` and `q < 1`.
* Kreps-Wilson consistency then forces a belief leaving out one label at one
  of the two inclusion sets of that class, for every inclusion probability.
* There the listener guesses, and type `(v, A)` gets at least
  `q R - (1 - q) (D + c)` by deferring to that turn. When this exceeds `R/2`,
  its value at the protected turn, deferring contradicts rationality there.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : LateLeakParameters} {late : Bool}

/-! ## Outcome laws -/

/-- The law of the final state of play from the initial state. -/
def lateLeakOutcomeLaw (G : LateLeakParameters) (late : Bool)
    (profile : LateLeakProfile G late) : PMF LateLeakState :=
  ((lateLeakModel G late).runBehavioralTerminalFrom (lateLeak_terminates G late) profile
    (lateLeakExecution G late).initHistory).map ExecutionProtocol.History.state

/-- The intended outcome: every type opens at the protected turn and the
listener gives the safe answer. -/
def lateLeakIntendedOutcome : PMF LateLeakState :=
  lateLeakPrior.map fun secret => .finished secret .protectedOpen .safe

theorem lateLeakOutcomeLaw_eq (G : LateLeakParameters) (late : Bool)
    (profile : LateLeakProfile G late) :
    lateLeakOutcomeLaw G late profile = (lateLeakFlow profile)^[5] (PMF.pure .initial) :=
  lateLeak_terminal_map_state _ profile _

theorem lateLeakIntendedOutcome_apply (secret : LateLeakType) :
    lateLeakIntendedOutcome (.finished secret .protectedOpen .safe) = lateLeakPrior secret :=
  pmf_map_apply_of_injective lateLeakPrior
    (f := fun secret => LateLeakState.finished secret .protectedOpen .safe)
    (fun _ _ same => (LateLeakState.finished.inj same).1) secret

/-- The outcome law's mass on a type opening at the protected turn and the
listener answering safely. -/
theorem lateLeakOutcomeLaw_protected_safe (profile : LateLeakProfile G late)
    (secret : LateLeakType) :
    (lateLeakOutcomeLaw G late profile (.finished secret .protectedOpen .safe)).toReal =
      (lateLeakPrior secret).toReal *
        (lateLeakOpenProb profile (.protectedTurn secret) *
          lateLeakSafeProb profile (.protectedSuccess secret.1)) := by
  classical
  let target : LateLeakState := .finished secret .protectedOpen .safe
  let indicator : LateLeakState → ℝ := fun state => if target = state then 1 else 0
  have read : (lateLeakOutcomeLaw G late profile target).toReal =
      lateLeakValue profile indicator (0 + 5) .initial := by
    rw [lateLeakValue, ← lateLeakOutcomeLaw_eq, expect_ite_eq, mul_one]
  have answer (other : LateLeakType) (resolution : LateLeakResolution) :
      lateLeakAnswerValue profile indicator other resolution =
        if other = secret ∧ resolution = .protectedOpen then
          lateLeakSafeProb profile (.protectedSuccess secret.1) else 0 := by
    by_cases hit : other = secret ∧ resolution = .protectedOpen
    · obtain ⟨rfl, rfl⟩ := hit
      simp only [and_self, ite_true]
      rw [lateLeakAnswerValue,
        lateLeak_expect_two_point _ (some (.reply .safe)) _ 0]
      · simp [indicator, target, lateLeakReplyOf, lateLeakSafeProb, lateLeakSignal]
      · intro choice supported different
        obtain ⟨reply, rfl, -⟩ := lateLeakReplyLaw_support profile _ choice supported
        have : reply ≠ .safe := fun same => different (by rw [same])
        simp [indicator, target, lateLeakReplyOf, Ne.symm this]
    · simp only [hit, ite_false]
      rw [lateLeakAnswerValue, ← expect_zero (lateLeakReplyLaw profile _)]
      apply expect_congr_on_support
      intro choice _
      simp only [indicator, target, LateLeakState.finished.injEq]
      split
      · rename_i same
        exact (hit ⟨same.1.symm, same.2.1.symm⟩).elim
      · rfl
  have protectedValue (other : LateLeakType) :
      lateLeakProtectedValue profile indicator other =
        if secret = other then
          lateLeakOpenProb profile (.protectedTurn secret) *
            lateLeakSafeProb profile (.protectedSuccess secret.1) else 0 := by
    simp only [lateLeakProtectedValue, lateLeakFirstValue, lateLeakSecondValue,
      lateLeakSendValue, answer]
    by_cases same : secret = other
    · subst same
      simp
    · simp [Ne.symm same, same]
  rw [read, lateLeakValue_initial]
  simp only [protectedValue]
  rw [expect_ite_eq]

/-- An outcome law equal to the intended one forces opening at the protected
turn and the safe answer there. -/
theorem lateLeak_intended_law_forces (profile : LateLeakProfile G late)
    (same : lateLeakOutcomeLaw G late profile = lateLeakIntendedOutcome) (secret : LateLeakType) :
    lateLeakOpenProb profile (.protectedTurn secret) = 1 ∧
      lateLeakSafeProb profile (.protectedSuccess secret.1) = 1 := by
  have mass := lateLeakOutcomeLaw_protected_safe profile secret
  rw [same, lateLeakIntendedOutcome_apply] at mass
  have positive : 0 < (lateLeakPrior secret).toReal :=
    ENNReal.toReal_pos (lateLeakPrior_ne_zero secret) (PMF.apply_ne_top _ _)
  have product : lateLeakOpenProb profile (.protectedTurn secret) *
      lateLeakSafeProb profile (.protectedSuccess secret.1) = 1 := by
    have := mass.symm
    rw [mul_eq_left₀ positive.ne'] at this
    exact this
  have p0 := lateLeakOpenProb_nonneg profile (.protectedTurn secret)
  have p1 := lateLeakOpenProb_le_one profile (.protectedTurn secret)
  have m0 := lateLeakSafeProb_nonneg profile (.protectedSuccess secret.1)
  have m1 := lateLeakSafeProb_le_one profile (.protectedSuccess secret.1)
  constructor <;> nlinarith

/-! ## Opposite preferences -/

theorem lateLeak_first_send_value (profile : LateLeakProfile G late) (secret : LateLeakType) :
    lateLeakSendValue profile (lateLeakStatePayoff G .sender) secret .firstIncluded .firstDropped =
      lateLeakInclusionProb G *
          (lateLeakSafeProb profile (.firstSuccess secret.1) * (G.reward / 2) +
            (1 - lateLeakSafeProb profile (.firstSuccess secret.1)) *
              lateLeakGuessGain G secret.2) +
        (1 - lateLeakInclusionProb G) *
          (lateLeakBitOneProb profile (.leakedFailure secret.1) * lateLeakBitOneGain G secret.2 +
            (1 - lateLeakBitOneProb profile (.leakedFailure secret.1)) *
              lateLeakBitZeroGain G secret.2 - G.forfeit - G.dropCharge) := by
  rw [lateLeakSendValue, lateLeak_sender_success_value profile secret .firstIncluded rfl,
    lateLeak_sender_failure_value profile secret .firstDropped rfl]
  simp only [lateLeakSignal, LateLeakResolution.droppedLate, ite_true]

theorem lateLeak_second_send_value (profile : LateLeakProfile G late) (secret : LateLeakType) :
    lateLeakSendValue profile (lateLeakStatePayoff G .sender) secret .secondIncluded
        .secondDropped =
      lateLeakInclusionProb G *
          (lateLeakSafeProb profile (.secondSuccess secret.1) * (G.reward / 2) +
            (1 - lateLeakSafeProb profile (.secondSuccess secret.1)) *
              lateLeakGuessGain G secret.2) +
        (1 - lateLeakInclusionProb G) *
          (lateLeakBitOneProb profile .silentFailure * lateLeakBitOneGain G secret.2 +
            (1 - lateLeakBitOneProb profile .silentFailure) * lateLeakBitZeroGain G secret.2 -
              G.forfeit - G.dropCharge) := by
  rw [lateLeakSendValue, lateLeak_sender_success_value profile secret .secondIncluded rfl,
    lateLeak_sender_failure_value profile secret .secondDropped rfl]
  simp only [lateLeakSignal, LateLeakResolution.droppedLate, ite_true]

/-- A label's preference for the first late turn over the second, given the
pull `pull` of the listener's answers after the two inclusions and the pull
`leak` of what the leak changes after a failure: labels `A` and `B` move
together under `pull` and apart under `leak`, and label `C` moves against
`pull`. -/
def lateLeakLabelPreference (pull leak : ℝ) : LateLeakLabel → ℝ
  | .a => pull + leak
  | .b => pull - leak
  | .c => -pull

/-- A nonzero leak pull gives one label a strict preference for the first late
turn and another a strict preference for the second, whatever the other
pull. -/
theorem lateLeak_opposite_label_preferences (pull leak : ℝ) (separates : leak ≠ 0) :
    ∃ sender holder, 0 < lateLeakLabelPreference pull leak sender ∧
      lateLeakLabelPreference pull leak holder < 0 := by
  rcases lt_or_gt_of_ne separates with negative | positive
  · rcases lt_trichotomy pull 0 with below | zero | above
    · exact ⟨.c, .a, by simp only [lateLeakLabelPreference]; linarith,
        by simp only [lateLeakLabelPreference]; linarith⟩
    · exact ⟨.b, .a, by simp only [lateLeakLabelPreference]; linarith,
        by simp only [lateLeakLabelPreference]; linarith⟩
    · exact ⟨.b, .c, by simp only [lateLeakLabelPreference]; linarith,
        by simp only [lateLeakLabelPreference]; linarith⟩
  · rcases lt_trichotomy pull 0 with below | zero | above
    · exact ⟨.c, .b, by simp only [lateLeakLabelPreference]; linarith,
        by simp only [lateLeakLabelPreference]; linarith⟩
    · exact ⟨.a, .b, by simp only [lateLeakLabelPreference]; linarith,
        by simp only [lateLeakLabelPreference]; linarith⟩
    · exact ⟨.a, .c, by simp only [lateLeakLabelPreference]; linarith,
        by simp only [lateLeakLabelPreference]; linarith⟩

/-- Every answer after a success acts on the sender along one direction, so a
type's preference for the first late turn over the second is its label's
preference under one pull from the listener's safe answers and one from the
leak. -/
private theorem send_preference (profile : LateLeakProfile G late) (secret : LateLeakType) :
    lateLeakSendValue profile (lateLeakStatePayoff G .sender) secret .firstIncluded
        .firstDropped -
      lateLeakSendValue profile (lateLeakStatePayoff G .sender) secret .secondIncluded
        .secondDropped =
      lateLeakLabelPreference
        (lateLeakInclusionProb G * (lateLeakSafeProb profile (.secondSuccess secret.1) -
          lateLeakSafeProb profile (.firstSuccess secret.1)) * (G.reward / 2))
        ((1 - lateLeakInclusionProb G) * (lateLeakBitOneProb profile (.leakedFailure secret.1) -
          lateLeakBitOneProb profile .silentFailure) * G.reward) secret.2 := by
  rw [lateLeak_first_send_value, lateLeak_second_send_value]
  obtain ⟨bit, label⟩ := secret
  cases label <;>
    simp only [lateLeakLabelPreference, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain,
      ite_true, ite_false, reduceCtorEq] <;>
    ring

/-- **Opposite strict preferences.** In every sequentially rational assessment
two types of one class strictly prefer opposite late turns, when the reward
scale is positive. -/
theorem lateLeak_opposite_preferences (reward_pos : 0 < G.reward)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    ∃ bit sender holder,
      lateLeakSendValue A.strategy (lateLeakStatePayoff G .sender) (bit, sender) .secondIncluded
          .secondDropped <
        lateLeakSendValue A.strategy (lateLeakStatePayoff G .sender) (bit, sender) .firstIncluded
          .firstDropped ∧
      lateLeakSendValue A.strategy (lateLeakStatePayoff G .sender) (bit, holder) .firstIncluded
          .firstDropped <
        lateLeakSendValue A.strategy (lateLeakStatePayoff G .sender) (bit, holder) .secondIncluded
          .secondDropped := by
  have dropped : (1 - lateLeakInclusionProb G) ≠ 0 :=
    (sub_pos.mpr (lateLeakInclusionProb_lt_one G)).ne'
  obtain ⟨bit, separates⟩ : ∃ bit, (1 - lateLeakInclusionProb G) *
      (lateLeakBitOneProb A.strategy (.leakedFailure bit) -
        lateLeakBitOneProb A.strategy .silentFailure) * G.reward ≠ 0 := by
    by_cases sure : lateLeakBitOneProb A.strategy .silentFailure = 1
    · refine ⟨false, ?_⟩
      rw [lateLeak_rational_leaked_failure rational (lateLeakLeakedFailureSite G false) false rfl,
        sure]
      exact mul_ne_zero (mul_ne_zero dropped (by norm_num)) reward_pos.ne'
    · refine ⟨true, ?_⟩
      rw [lateLeak_rational_leaked_failure rational (lateLeakLeakedFailureSite G true) true rfl]
      simp only [↓reduceIte]
      exact mul_ne_zero (mul_ne_zero dropped (sub_ne_zero.mpr (Ne.symm sure))) reward_pos.ne'
  obtain ⟨sender, holder, prefers, avoids⟩ := lateLeak_opposite_label_preferences _ _ separates
  refine ⟨bit, sender, holder, ?_, ?_⟩
  · have identity := send_preference A.strategy (bit, sender)
    linarith
  · have identity := send_preference A.strategy (bit, holder)
    linarith

/-! ## Deferring after a guessing listener -/

/-- The value of the protected turn when its type opens there. -/
private theorem protected_value_of_open (profile : LateLeakProfile G late) (secret : LateLeakType)
    (opens : lateLeakOpenProb profile (.protectedTurn secret) = 1) :
    lateLeakProtectedValue profile (lateLeakStatePayoff G .sender) secret =
      lateLeakAnswerValue profile (lateLeakStatePayoff G .sender) secret .protectedOpen := by
  rw [lateLeakProtectedValue, opens]
  ring

/-- If the listener guesses after a late inclusion of a type `(v, A)` that
opens at the protected turn, and the safe answer follows its protected
opening, deferring to that late turn pays when `q R - (1 - q) (D + c) > R/2`. -/
private theorem deferral_pays (pays : G.DeferralPays) (profile : LateLeakProfile G late)
    (bit : Bool) (failure : LateLeakSignal)
    (safe : lateLeakSafeProb profile (.protectedSuccess bit) = 1) :
    lateLeakSafeProb profile (.protectedSuccess bit) * (G.reward / 2) +
        (1 - lateLeakSafeProb profile (.protectedSuccess bit)) * G.reward <
      lateLeakInclusionProb G * G.reward +
        (1 - lateLeakInclusionProb G) *
          (lateLeakBitOneProb profile failure * G.reward - G.forfeit - G.dropCharge) := by
  rw [safe]
  have leak : 0 ≤ (1 - lateLeakInclusionProb G) * (lateLeakBitOneProb profile failure * G.reward) :=
    mul_nonneg (sub_nonneg.mpr (lateLeakInclusionProb_lt_one G).le)
      (mul_nonneg (lateLeakBitOneProb_nonneg profile failure) pays.reward_pos.le)
  have margin := pays.guess_beats_safe
  nlinarith

/-- If the listener guesses after a first-turn inclusion, type `(v, A)` gains
by deferring to the first late turn. -/
theorem lateLeak_defer_first (pays : G.DeferralPays)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (same : lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome) (bit : Bool)
    (guessing : lateLeakSafeProb A.strategy (.firstSuccess bit) = 0) : False := by
  let secret : LateLeakType := (bit, .a)
  obtain ⟨opens, safe⟩ := lateLeak_intended_law_forces A.strategy same secret
  let wait := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) false
    ⟨false, rfl, rfl⟩
  let deviation := lateLeakCommitOpen wait (.firstLate secret) true ⟨true, rfl⟩
  have optimal := lateLeak_sender_rational rational
    (lateLeakSenderSite G true (lateLeakTypeHistory G true secret) rfl)
    (state := .protectedTurn secret) rfl deviation
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn, lateLeakValue_protectedTurn,
    protected_value_of_open _ _ opens, lateLeak_sender_success_value _ _ _ rfl, lateLeakSignal,
    lateLeakProtectedValue, lateLeakFirstValue,
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_self, lateLeakOpenProb_update_commit_self,
    lateLeakSendValue_update_sender, lateLeak_first_send_value] at optimal
  simp only [Bool.false_eq_true, ite_false, ite_true, zero_mul, sub_zero, one_mul, zero_add,
    sub_self, add_zero] at optimal
  rw [show (secret.1) = bit from rfl, guessing] at optimal
  simp only [secret, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain,
    reduceCtorEq, ite_true, ite_false] at optimal
  have gain := deferral_pays pays A.strategy bit (.leakedFailure bit) safe
  linarith

/-- If the listener guesses after a second-turn inclusion, type `(v, A)` gains
by deferring to the second late turn. -/
theorem lateLeak_defer_second (pays : G.DeferralPays)
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (same : lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome) (bit : Bool)
    (guessing : lateLeakSafeProb A.strategy (.secondSuccess bit) = 0) : False := by
  let secret : LateLeakType := (bit, .a)
  obtain ⟨opens, safe⟩ := lateLeak_intended_law_forces A.strategy same secret
  let wait := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) false
    ⟨false, rfl, rfl⟩
  let hold := lateLeakCommitOpen wait (.firstLate secret) false ⟨false, rfl⟩
  let deviation := lateLeakCommitOpen hold (.secondLate secret) true ⟨true, rfl⟩
  have optimal := lateLeak_sender_rational rational
    (lateLeakSenderSite G true (lateLeakTypeHistory G true secret) rfl)
    (state := .protectedTurn secret) rfl deviation
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn, lateLeakValue_protectedTurn,
    protected_value_of_open _ _ opens, lateLeak_sender_success_value _ _ _ rfl, lateLeakSignal,
    lateLeakProtectedValue, lateLeakFirstValue, lateLeakSecondValue,
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_self,
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_self, lateLeakOpenProb_update_commit_self,
    lateLeakSendValue_update_sender, lateLeakSendValue_update_sender,
    lateLeak_second_send_value] at optimal
  simp only [Bool.false_eq_true, ite_false, ite_true, zero_mul, sub_zero, one_mul, zero_add,
    sub_self, add_zero] at optimal
  rw [show (secret.1) = bit from rfl, guessing] at optimal
  simp only [secret, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain,
    reduceCtorEq, ite_true, ite_false] at optimal
  have gain := deferral_pays pays A.strategy bit .silentFailure safe
  linarith

/-- **No sequential equilibrium of the late-turn game has the intended
outcome law**, when deferring pays: `R > 0`, `q (D - R) > (1 - q) c` and
`q R - (1 - q) (D + c) > R/2`. -/
theorem lateLeak_no_intended_equilibrium (pays : G.DeferralPays)
    (A : (lateLeakModel G true).BehavioralAssessment)
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    lateLeakOutcomeLaw G true A.strategy ≠ lateLeakIntendedOutcome := by
  intro same
  obtain ⟨rational, consistent⟩ := equilibrium
  obtain ⟨bit, sender, holder, senderPrefers, holderPrefers⟩ :=
    lateLeak_opposite_preferences pays.reward_pos rational
  have sends := (lateLeak_rational_first_turn pays rational (bit, sender)).1 senderPrefers
  have holds := (lateLeak_rational_first_turn pays rational (bit, holder)).2 holderPrefers
  have holderSends := lateLeak_rational_second_sends pays rational (bit, holder)
  rcases lateLeak_consistent_face consistent bit sender holder sends holds holderSends with
    zero | zero
  · have reward := lateLeak_guess_reward_zero A (lateLeakFirstSuccessSite G bit)
      (.firstSuccess bit) rfl rfl _ (bit, holder) .firstIncluded rfl zero
    exact lateLeak_defer_first pays rational same bit
      (lateLeak_rational_guesses rational _ _ rfl rfl _ reward)
  · have reward := lateLeak_guess_reward_zero A (lateLeakSecondSuccessSite G bit)
      (.secondSuccess bit) rfl rfl _ (bit, sender) .secondIncluded rfl zero
    exact lateLeak_defer_second pays rational same bit
      (lateLeak_rational_guesses rational _ _ rfl rfl _ reward)

end Vegas
