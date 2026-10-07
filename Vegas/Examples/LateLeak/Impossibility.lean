/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Consistency

/-! # No sequential equilibrium of the late-turn game has the intended outcome

Suppose a sequential equilibrium of the late-turn game has the intended
outcome: every type opens at the protected turn and the listener answers
safely.

* Every answer after a success acts on the sender along one direction, so the
  sender's late-turn values depend on the listener only through its safe
  probabilities and its bit guesses after failures.
* Whatever the listener answers after an unseen failure, the leak after a
  first-turn failure separates labels `A` and `B` in some class of the
  committed bit, so two types of that class strictly prefer opposite late
  turns, for every choice of the listener's answers after successes.
* Kreps-Wilson consistency then forces a belief leaving out one label at one
  of the two inclusion sets of that class.
* There the listener guesses, and type `(v, A)` gains `189/100 > 1` by
  deferring to that turn, contradicting rationality at the protected turn.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {late : Bool}

/-! ## Outcome laws -/

/-- The law of the final state of play from the initial state. -/
def lateLeakOutcomeLaw (late : Bool) (profile : LateLeakProfile late) : PMF LateLeakState :=
  ((lateLeakModel late).runBehavioralTerminalFrom (lateLeak_terminates late) profile
    (lateLeakExecution late).initHistory).map ExecutionProtocol.History.state

/-- The intended outcome: every type opens at the protected turn and the
listener gives the safe answer. -/
def lateLeakIntendedOutcome : PMF LateLeakState :=
  lateLeakPrior.map fun secret => .finished secret .protectedOpen .safe

theorem lateLeakOutcomeLaw_eq (late : Bool) (profile : LateLeakProfile late) :
    lateLeakOutcomeLaw late profile = (lateLeakFlow profile)^[5] (PMF.pure .initial) :=
  lateLeak_terminal_map_state _ profile _

theorem lateLeakIntendedOutcome_apply (secret : LateLeakType) :
    lateLeakIntendedOutcome (.finished secret .protectedOpen .safe) = lateLeakPrior secret :=
  pmf_map_apply_of_injective lateLeakPrior
    (f := fun secret => LateLeakState.finished secret .protectedOpen .safe)
    (fun _ _ same => (LateLeakState.finished.inj same).1) secret

/-- The outcome law's mass on a type opening at the protected turn and the
listener answering safely. -/
theorem lateLeakOutcomeLaw_protected_safe (profile : LateLeakProfile late)
    (secret : LateLeakType) :
    (lateLeakOutcomeLaw late profile (.finished secret .protectedOpen .safe)).toReal =
      (lateLeakPrior secret).toReal *
        (lateLeakOpenProb profile (.protectedTurn secret) *
          lateLeakSafeProb profile (.protectedSuccess secret.1)) := by
  classical
  let target : LateLeakState := .finished secret .protectedOpen .safe
  let indicator : LateLeakState → ℝ := fun state => if target = state then 1 else 0
  have read : (lateLeakOutcomeLaw late profile target).toReal =
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
theorem lateLeak_intended_law_forces (profile : LateLeakProfile late)
    (same : lateLeakOutcomeLaw late profile = lateLeakIntendedOutcome) (secret : LateLeakType) :
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

theorem lateLeak_first_send_value (profile : LateLeakProfile late) (secret : LateLeakType) :
    lateLeakSendValue profile (lateLeakStatePayoff .sender) secret .firstIncluded .firstDropped =
      99 / 100 * (lateLeakSafeProb profile (.firstSuccess secret.1) +
          (1 - lateLeakSafeProb profile (.firstSuccess secret.1)) * lateLeakGuessGain secret.2) +
        1 / 100 * (lateLeakBitOneProb profile (.leakedFailure secret.1) *
            lateLeakBitOneGain secret.2 +
          (1 - lateLeakBitOneProb profile (.leakedFailure secret.1)) *
            lateLeakBitZeroGain secret.2 - 9) := by
  rw [lateLeakSendValue, lateLeak_sender_success_value profile secret .firstIncluded rfl,
    lateLeak_sender_failure_value profile secret .firstDropped rfl]
  simp only [lateLeakSignal, LateLeakResolution.droppedLate, ite_true, lateLeakInclusionProb]
  ring

theorem lateLeak_second_send_value (profile : LateLeakProfile late) (secret : LateLeakType) :
    lateLeakSendValue profile (lateLeakStatePayoff .sender) secret .secondIncluded
        .secondDropped =
      99 / 100 * (lateLeakSafeProb profile (.secondSuccess secret.1) +
          (1 - lateLeakSafeProb profile (.secondSuccess secret.1)) * lateLeakGuessGain secret.2) +
        1 / 100 * (lateLeakBitOneProb profile .silentFailure * lateLeakBitOneGain secret.2 +
          (1 - lateLeakBitOneProb profile .silentFailure) * lateLeakBitZeroGain secret.2 - 9) := by
  rw [lateLeakSendValue, lateLeak_sender_success_value profile secret .secondIncluded rfl,
    lateLeak_sender_failure_value profile secret .secondDropped rfl]
  simp only [lateLeakSignal, LateLeakResolution.droppedLate, ite_true, lateLeakInclusionProb]
  ring

/-- **Opposite strict preferences.** In every sequentially rational assessment
two types of one class strictly prefer opposite late turns. -/
theorem lateLeak_opposite_preferences {A : (lateLeakModel true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates true) (lateLeakPayoff true)) :
    ∃ bit sender holder,
      lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) (bit, sender) .secondIncluded
          .secondDropped <
        lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) (bit, sender) .firstIncluded
          .firstDropped ∧
      lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) (bit, holder) .firstIncluded
          .firstDropped <
        lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) (bit, holder) .secondIncluded
          .secondDropped := by
  simp only [lateLeak_first_send_value, lateLeak_second_send_value]
  have θ0 := lateLeakBitOneProb_nonneg A.strategy .silentFailure
  have θ1 := lateLeakBitOneProb_le_one A.strategy .silentFailure
  by_cases unsure : lateLeakBitOneProb A.strategy .silentFailure < 1
  · have leaked := lateLeak_rational_leaked_failure rational (lateLeakLeakedFailureSite true)
      true rfl
    have f0 := lateLeakSafeProb_nonneg A.strategy (.firstSuccess true)
    have f1 := lateLeakSafeProb_le_one A.strategy (.firstSuccess true)
    have s0 := lateLeakSafeProb_nonneg A.strategy (.secondSuccess true)
    have s1 := lateLeakSafeProb_le_one A.strategy (.secondSuccess true)
    by_cases low : 99 / 100 * (lateLeakSafeProb A.strategy (.secondSuccess true) -
        lateLeakSafeProb A.strategy (.firstSuccess true)) +
        1 / 50 * (1 - lateLeakBitOneProb A.strategy .silentFailure) ≤ 0
    · refine ⟨true, .c, .b, ?_, ?_⟩ <;>
        norm_num [leaked, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain] <;>
        linarith
    by_cases high : 0 ≤ 99 / 100 * (lateLeakSafeProb A.strategy (.secondSuccess true) -
        lateLeakSafeProb A.strategy (.firstSuccess true)) -
        1 / 50 * (1 - lateLeakBitOneProb A.strategy .silentFailure)
    · refine ⟨true, .a, .c, ?_, ?_⟩ <;>
        norm_num [leaked, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain] <;>
        linarith
    · refine ⟨true, .a, .b, ?_, ?_⟩ <;>
        norm_num [leaked, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain] <;>
        linarith
  · have sure : lateLeakBitOneProb A.strategy .silentFailure = 1 := by linarith
    have leaked := lateLeak_rational_leaked_failure rational (lateLeakLeakedFailureSite false)
      false rfl
    have f0 := lateLeakSafeProb_nonneg A.strategy (.firstSuccess false)
    have f1 := lateLeakSafeProb_le_one A.strategy (.firstSuccess false)
    have s0 := lateLeakSafeProb_nonneg A.strategy (.secondSuccess false)
    have s1 := lateLeakSafeProb_le_one A.strategy (.secondSuccess false)
    by_cases low : 99 / 100 * (lateLeakSafeProb A.strategy (.secondSuccess false) -
        lateLeakSafeProb A.strategy (.firstSuccess false)) + 1 / 50 ≤ 0
    · refine ⟨false, .c, .a, ?_, ?_⟩ <;>
        norm_num [leaked, sure, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain] <;>
        linarith
    by_cases high : 0 ≤ 99 / 100 * (lateLeakSafeProb A.strategy (.secondSuccess false) -
        lateLeakSafeProb A.strategy (.firstSuccess false)) - 1 / 50
    · refine ⟨false, .b, .c, ?_, ?_⟩ <;>
        norm_num [leaked, sure, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain] <;>
        linarith
    · refine ⟨false, .b, .a, ?_, ?_⟩ <;>
        norm_num [leaked, sure, lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain] <;>
        linarith

/-! ## Deferring after a guessing listener -/

private theorem deferred_gain (profile : LateLeakProfile late) (bit : Bool)
    (failure : LateLeakSignal) :
    1 < 99 / 100 * (0 + (1 - 0) * lateLeakGuessGain (bit, LateLeakLabel.a).2) +
      1 / 100 * (lateLeakBitOneProb profile failure * lateLeakBitOneGain (bit, LateLeakLabel.a).2 +
        (1 - lateLeakBitOneProb profile failure) * lateLeakBitZeroGain (bit, LateLeakLabel.a).2 -
          9) := by
  have b0 := lateLeakBitOneProb_nonneg profile failure
  have b1 := lateLeakBitOneProb_le_one profile failure
  norm_num [lateLeakGuessGain, lateLeakBitOneGain, lateLeakBitZeroGain]
  linarith

/-- The value of the protected turn when its type opens there. -/
private theorem protected_value_of_open (profile : LateLeakProfile late) (secret : LateLeakType)
    (opens : lateLeakOpenProb profile (.protectedTurn secret) = 1) :
    lateLeakProtectedValue profile (lateLeakStatePayoff .sender) secret =
      lateLeakAnswerValue profile (lateLeakStatePayoff .sender) secret .protectedOpen := by
  rw [lateLeakProtectedValue, opens]
  ring

/-- If the listener guesses after a first-turn inclusion, type `(v, A)` gains
by deferring to the first late turn. -/
theorem lateLeak_defer_first {A : (lateLeakModel true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates true) (lateLeakPayoff true))
    (same : lateLeakOutcomeLaw true A.strategy = lateLeakIntendedOutcome) (bit : Bool)
    (guessing : lateLeakSafeProb A.strategy (.firstSuccess bit) = 0) : False := by
  let secret : LateLeakType := (bit, .a)
  obtain ⟨opens, safe⟩ := lateLeak_intended_law_forces A.strategy same secret
  let wait := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) false
    ⟨false, rfl, rfl⟩
  let deviation := lateLeakCommitOpen wait (.firstLate secret) true ⟨true, rfl⟩
  have optimal := lateLeak_sender_rational rational
    (lateLeakSenderSite true (lateLeakTypeHistory true secret) rfl)
    (state := .protectedTurn secret) rfl deviation
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn, lateLeakValue_protectedTurn,
    protected_value_of_open _ _ opens, lateLeak_sender_success_value _ _ _ rfl, lateLeakSignal,
    safe, lateLeakProtectedValue, lateLeakFirstValue,
    lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _ (by simp),
    lateLeakOpenProb_update_commit_self, lateLeakOpenProb_update_commit_self,
    lateLeakSendValue_update_sender, lateLeak_first_send_value] at optimal
  simp only [Bool.false_eq_true, ite_false, ite_true, zero_mul, sub_zero, one_mul, zero_add,
    sub_self, add_zero] at optimal
  rw [show (secret.1) = bit from rfl, guessing] at optimal
  have gain := deferred_gain A.strategy bit (.leakedFailure bit)
  norm_num [lateLeakGuessGain] at optimal gain ⊢
  linarith

/-- If the listener guesses after a second-turn inclusion, type `(v, A)` gains
by deferring to the second late turn. -/
theorem lateLeak_defer_second {A : (lateLeakModel true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates true) (lateLeakPayoff true))
    (same : lateLeakOutcomeLaw true A.strategy = lateLeakIntendedOutcome) (bit : Bool)
    (guessing : lateLeakSafeProb A.strategy (.secondSuccess bit) = 0) : False := by
  let secret : LateLeakType := (bit, .a)
  obtain ⟨opens, safe⟩ := lateLeak_intended_law_forces A.strategy same secret
  let wait := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) false
    ⟨false, rfl, rfl⟩
  let hold := lateLeakCommitOpen wait (.firstLate secret) false ⟨false, rfl⟩
  let deviation := lateLeakCommitOpen hold (.secondLate secret) true ⟨true, rfl⟩
  have optimal := lateLeak_sender_rational rational
    (lateLeakSenderSite true (lateLeakTypeHistory true secret) rfl)
    (state := .protectedTurn secret) rfl deviation
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn, lateLeakValue_protectedTurn,
    protected_value_of_open _ _ opens, lateLeak_sender_success_value _ _ _ rfl, lateLeakSignal,
    safe, lateLeakProtectedValue, lateLeakFirstValue, lateLeakSecondValue,
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
  have gain := deferred_gain A.strategy bit .silentFailure
  norm_num [lateLeakGuessGain] at optimal gain ⊢
  linarith

/-- **No sequential equilibrium of the late-turn game has the intended
outcome law.** -/
theorem lateLeak_no_intended_equilibrium (A : (lateLeakModel true).BehavioralAssessment)
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain true) (lateLeak_terminates true)
      (lateLeakPayoff true)) :
    lateLeakOutcomeLaw true A.strategy ≠ lateLeakIntendedOutcome := by
  intro same
  obtain ⟨rational, consistent⟩ := equilibrium
  obtain ⟨bit, sender, holder, senderPrefers, holderPrefers⟩ :=
    lateLeak_opposite_preferences rational
  have sends := (lateLeak_rational_first_turn rational (bit, sender)).1 senderPrefers
  have holds := (lateLeak_rational_first_turn rational (bit, holder)).2 holderPrefers
  have holderSends := lateLeak_rational_second_sends rational (bit, holder)
  rcases lateLeak_consistent_face consistent bit sender holder sends holds holderSends with
    zero | zero
  · have reward := lateLeak_guess_reward_zero A (lateLeakFirstSuccessSite bit) (.firstSuccess bit)
      rfl rfl _ (bit, holder) .firstIncluded rfl zero
    exact lateLeak_defer_first rational same bit
      (lateLeak_rational_guesses rational _ _ rfl rfl _ reward)
  · have reward := lateLeak_guess_reward_zero A (lateLeakSecondSuccessSite bit)
      (.secondSuccess bit) rfl rfl _ (bit, sender) .secondIncluded rfl zero
    exact lateLeak_defer_second rational same bit
      (lateLeak_rational_guesses rational _ _ rfl rfl _ reward)

end Vegas
