/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Play

/-! # Incentives in the late-turn game

Every listener answer after a successful opening acts on the sender along one
direction: all label guesses pay the sender alike. The sender's values at its
turns are therefore affine in the listener's probability of the safe answer
and of the bit guess `1`. This file computes those values and reads off what
sequential rationality forces at each information set.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {late : Bool}

theorem lateLeak_toReal_le_one {α : Type*} (μ : PMF α) (x : α) : (μ x).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one μ x)

/-! ## The listener's options -/

theorem lateLeakReplyLaw_support (profile : LateLeakProfile late) (signal : LateLeakSignal)
    (choice : Option LateLeakMove)
    (supported : choice ∈ (lateLeakReplyLaw profile signal).support) :
    ∃ answer, choice = some (.reply answer) ∧ answer.fits signal := by
  rw [lateLeakReplyLaw, PMF.mem_support_map_iff] at supported
  obtain ⟨option, _, rfl⟩ := supported
  exact option.2

theorem lateLeakReplyLaw_apply (profile : LateLeakProfile late) (signal : LateLeakSignal)
    (answer : LateLeakAnswer) (fits : answer.fits signal) :
    lateLeakReplyLaw profile signal (some (.reply answer)) =
      profile .listener (.asked signal) ⟨some (.reply answer), ⟨answer, rfl, fits⟩⟩ :=
  pmf_map_apply_of_injective _ Subtype.val_injective
    (⟨some (.reply answer), ⟨answer, rfl, fits⟩⟩ :
      (lateLeakModel late).Choice .listener (.asked signal))

theorem lateLeakOpeningLaw_apply (profile : LateLeakProfile late) (state : LateLeakState)
    (now : Bool) (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu late (.full state)) :
    lateLeakOpeningLaw profile state (some (.opening now)) =
      profile .sender (.full state) ⟨some (.opening now), allowed⟩ :=
  pmf_map_apply_of_injective _ Subtype.val_injective
    (⟨some (.opening now), allowed⟩ : (lateLeakModel late).Choice .sender (.full state))

/-- At one of the sender's states, waiting has the remaining probability. -/
theorem lateLeakOpeningLaw_wait (profile : LateLeakProfile late) (state : LateLeakState)
    (acting : state.actor = some .sender) :
    (lateLeakOpeningLaw profile state (some (.opening false))).toReal =
      1 - lateLeakOpenProb profile state := by
  classical
  have computed := lateLeak_expect_two_point (lateLeakOpeningLaw profile state)
    (some (.opening true))
    (fun choice => if some (LateLeakMove.opening false) = choice then 1 else 0)
    1 (fun choice supported different => by
      obtain ⟨now, rfl⟩ := lateLeakOpeningLaw_support profile state acting choice supported
      cases now
      · simp
      · exact (different rfl).elim)
  rw [expect_ite_eq] at computed
  simpa [lateLeakOpenProb] using computed

theorem lateLeakOpenProb_nonneg (profile : LateLeakProfile late) (state : LateLeakState) :
    0 ≤ lateLeakOpenProb profile state := ENNReal.toReal_nonneg

theorem lateLeakOpenProb_le_one (profile : LateLeakProfile late) (state : LateLeakState) :
    lateLeakOpenProb profile state ≤ 1 := lateLeak_toReal_le_one _ _

theorem lateLeakSafeProb_nonneg (profile : LateLeakProfile late) (signal : LateLeakSignal) :
    0 ≤ lateLeakSafeProb profile signal := ENNReal.toReal_nonneg

theorem lateLeakSafeProb_le_one (profile : LateLeakProfile late) (signal : LateLeakSignal) :
    lateLeakSafeProb profile signal ≤ 1 := lateLeak_toReal_le_one _ _

theorem lateLeakBitOneProb_nonneg (profile : LateLeakProfile late) (signal : LateLeakSignal) :
    0 ≤ lateLeakBitOneProb profile signal := ENNReal.toReal_nonneg

theorem lateLeakBitOneProb_le_one (profile : LateLeakProfile late) (signal : LateLeakSignal) :
    lateLeakBitOneProb profile signal ≤ 1 := lateLeak_toReal_le_one _ _

/-! ## The sender's values -/

/-- What a label guess pays the sender: `R` for labels `A` and `B`. -/
def lateLeakGuessGain (label : LateLeakLabel) : ℝ :=
  if label = .c then 0 else 2

/-- What the bit guess `1` pays the sender after a failure. -/
def lateLeakBitOneGain (label : LateLeakLabel) : ℝ :=
  if label = .a then 2 else 0

/-- What the bit guess `0` pays the sender after a failure. -/
def lateLeakBitZeroGain (label : LateLeakLabel) : ℝ :=
  if label = .b then 2 else 0

theorem lateLeak_sender_success_value (profile : LateLeakProfile late) (secret : LateLeakType)
    (resolution : LateLeakResolution) (succeeded : resolution.succeeded = true) :
    lateLeakAnswerValue profile (lateLeakStatePayoff .sender) secret resolution =
      lateLeakSafeProb profile (lateLeakSignal secret resolution) +
        (1 - lateLeakSafeProb profile (lateLeakSignal secret resolution)) *
          lateLeakGuessGain secret.2 := by
  have dropped : resolution.droppedLate = false := by
    cases resolution <;> simp_all [LateLeakResolution.succeeded, LateLeakResolution.droppedLate]
  rw [lateLeakAnswerValue, lateLeak_expect_two_point _ (some (.reply .safe)) _
    (lateLeakGuessGain secret.2)]
  · simp only [lateLeakReplyOf, lateLeakStatePayoff, lateLeakSenderPayoff, lateLeakSenderBase,
      succeeded, dropped, ite_true, Bool.false_eq_true, ite_false, sub_zero, lateLeakSafeProb,
      mul_one]
  · intro choice supported different
    obtain ⟨answer, rfl, fits⟩ := lateLeakReplyLaw_support profile _ choice supported
    cases answer with
    | safe => exact (different rfl).elim
    | guess label =>
        cases label <;>
          simp [lateLeakReplyOf, lateLeakStatePayoff, lateLeakSenderPayoff, lateLeakSenderBase,
            succeeded, dropped, lateLeakGuessGain]
    | failure bit =>
        cases resolution <;>
          simp_all [LateLeakAnswer.fits, lateLeakSignal, LateLeakSignal.success,
            LateLeakResolution.succeeded]

theorem lateLeak_sender_failure_value (profile : LateLeakProfile late) (secret : LateLeakType)
    (resolution : LateLeakResolution) (failed : resolution.succeeded = false) :
    lateLeakAnswerValue profile (lateLeakStatePayoff .sender) secret resolution =
      lateLeakBitOneProb profile (lateLeakSignal secret resolution) *
          lateLeakBitOneGain secret.2 +
        (1 - lateLeakBitOneProb profile (lateLeakSignal secret resolution)) *
          lateLeakBitZeroGain secret.2 - 6 - (if resolution.droppedLate then 3 else 0) := by
  rw [lateLeakAnswerValue, lateLeak_expect_two_point _ (some (.reply (.failure true))) _
    (lateLeakBitZeroGain secret.2 - 6 - (if resolution.droppedLate then 3 else 0))]
  · cases label : secret.2 <;>
      simp [lateLeakReplyOf, lateLeakStatePayoff, lateLeakSenderPayoff, lateLeakSenderBase,
        failed, lateLeakBitOneProb, lateLeakBitOneGain, lateLeakBitZeroGain, label] <;> ring
  · intro choice supported different
    obtain ⟨answer, rfl, fits⟩ := lateLeakReplyLaw_support profile _ choice supported
    cases answer with
    | failure bit =>
        cases bit
        · cases label : secret.2 <;>
            simp [lateLeakReplyOf, lateLeakStatePayoff, lateLeakSenderPayoff,
              lateLeakSenderBase, failed, lateLeakBitZeroGain, label]
        · exact (different rfl).elim
    | _ =>
        cases resolution <;>
          simp_all [LateLeakAnswer.fits, lateLeakSignal, LateLeakSignal.success,
            LateLeakResolution.succeeded]

/-- Never opening is worse than sending at the second late turn. -/
theorem lateLeak_send_beats_withhold (profile : LateLeakProfile late) (secret : LateLeakType) :
    lateLeakAnswerValue profile (lateLeakStatePayoff .sender) secret .withheld <
      lateLeakSendValue profile (lateLeakStatePayoff .sender) secret .secondIncluded
        .secondDropped := by
  rw [lateLeakSendValue, lateLeak_sender_success_value profile secret .secondIncluded rfl,
    lateLeak_sender_failure_value profile secret .secondDropped rfl,
    lateLeak_sender_failure_value profile secret .withheld rfl]
  simp only [lateLeakSignal, LateLeakResolution.droppedLate, ite_true, Bool.false_eq_true,
    ite_false, lateLeakInclusionProb]
  have m0 := lateLeakSafeProb_nonneg profile (.secondSuccess secret.1)
  have m1 := lateLeakSafeProb_le_one profile (.secondSuccess secret.1)
  have b0 := lateLeakBitOneProb_nonneg profile .silentFailure
  have b1 := lateLeakBitOneProb_le_one profile .silentFailure
  have g0 : 0 ≤ lateLeakGuessGain secret.2 := by cases secret.2 <;> norm_num [lateLeakGuessGain]
  have o0 : 0 ≤ lateLeakBitOneGain secret.2 := by
    cases secret.2 <;> norm_num [lateLeakBitOneGain]
  have o1 : lateLeakBitOneGain secret.2 ≤ 2 := by
    cases secret.2 <;> norm_num [lateLeakBitOneGain]
  have z0 : 0 ≤ lateLeakBitZeroGain secret.2 := by
    cases secret.2 <;> norm_num [lateLeakBitZeroGain]
  have z1 : lateLeakBitZeroGain secret.2 ≤ 2 := by
    cases secret.2 <;> norm_num [lateLeakBitZeroGain]
  nlinarith [mul_nonneg (sub_nonneg.mpr m1) g0, mul_nonneg b0 o0, mul_nonneg (sub_nonneg.mpr b1) z0,
    mul_le_mul_of_nonneg_left o1 b0, mul_le_mul_of_nonneg_left z1 (sub_nonneg.mpr b1)]

/-! ## Updating the sender's policy -/

theorem lateLeakOpenProb_update (profile : LateLeakProfile late)
    (policy : (lateLeakModel late).BehavioralPolicy .sender) (state : LateLeakState) :
    lateLeakOpenProb (lateLeakUpdate profile .sender policy) state =
      (((policy (.full state)).map Subtype.val) (some (.opening true))).toReal := by
  rw [lateLeakOpenProb, lateLeakOpeningLaw_update_sender]

theorem lateLeakOpenProb_update_commit_self (profile : LateLeakProfile late)
    (policy : (lateLeakModel late).BehavioralPolicy .sender) (state : LateLeakState) (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu late (.full state)) :
    lateLeakOpenProb (lateLeakUpdate profile .sender (lateLeakCommitOpen policy state now allowed))
        state = if now then 1 else 0 := by
  rw [lateLeakOpenProb_update, lateLeakCommitOpen_self]
  cases now <;> simp [PMF.pure_apply]

theorem lateLeakOpenProb_update_commit_of_ne (profile : LateLeakProfile late)
    (policy : (lateLeakModel late).BehavioralPolicy .sender) (state other : LateLeakState)
    (now : Bool) (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu late (.full state))
    (different : other ≠ state) :
    lateLeakOpenProb (lateLeakUpdate profile .sender (lateLeakCommitOpen policy state now allowed))
        other = lateLeakOpenProb (lateLeakUpdate profile .sender policy) other := by
  rw [lateLeakOpenProb_update, lateLeakOpenProb_update,
    lateLeakCommitOpen_of_ne policy state other now allowed different]

/-! ## Rational play at the sender's late turns -/

theorem lateLeak_sender_open_allowed (late : Bool) (state : LateLeakState)
    (acting : state.actor = some .sender) :
    some (LateLeakMove.opening true) ∈ lateLeakMenu late (.full state) := by
  cases state with
  | protectedTurn secret => exact ⟨true, rfl, by simp⟩
  | firstLate secret => exact ⟨true, rfl⟩
  | secondLate secret => exact ⟨true, rfl⟩
  | _ => simp [LateLeakState.actor] at acting

theorem lateLeak_not_finished_of_actor {state : LateLeakState} {who : LateLeakRole}
    (acting : state.actor = some who) : ¬ state.IsFinished := by
  cases state <;> simp_all [LateLeakState.actor, LateLeakState.IsFinished]

/-- The sender's information site at a state reached by a history. -/
def lateLeakSenderSite (late : Bool) (history : (lateLeakExecution late).History)
    (acting : history.state.actor = some .sender) :
    (lateLeakModel late).InformationSite .sender :=
  lateLeakSite late .sender history (.opening true)
    (lateLeak_sender_open_allowed late history.state acting)
    (lateLeak_not_finished_of_actor acting)

/-- A sequentially rational sender sends at the second late turn. -/
theorem lateLeak_rational_second_sends {A : (lateLeakModel true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates true) (lateLeakPayoff true))
    (secret : LateLeakType) : lateLeakOpenProb A.strategy (.secondLate secret) = 1 := by
  have optimal := lateLeak_sender_rational rational
    (lateLeakSenderSite true (lateLeakSecondHistory secret) rfl) (state := .secondLate secret) rfl
    (lateLeakCommitOpen (A.strategy .sender) (.secondLate secret) true ⟨true, rfl⟩)
  rw [show (5 : ℕ) = 3 + 2 from rfl, lateLeakValue_secondLate, lateLeakValue_secondLate,
    lateLeakSecondValue, lateLeakSecondValue, lateLeakOpenProb_update_commit_self,
    lateLeakSendValue_update_sender] at optimal
  simp only [ite_true, sub_self, zero_mul, add_zero, one_mul] at optimal
  have better := lateLeak_send_beats_withhold A.strategy secret
  have p0 := lateLeakOpenProb_nonneg A.strategy (.secondLate secret)
  have p1 := lateLeakOpenProb_le_one A.strategy (.secondLate secret)
  nlinarith

/-- The value of the first late turn when the sender sends at the second. -/
theorem lateLeakFirstValue_of_second_sends (profile : LateLeakProfile late)
    (payoff : LateLeakState → ℝ) (secret : LateLeakType)
    (sends : lateLeakOpenProb profile (.secondLate secret) = 1) :
    lateLeakFirstValue profile payoff secret =
      lateLeakOpenProb profile (.firstLate secret) *
          lateLeakSendValue profile payoff secret .firstIncluded .firstDropped +
        (1 - lateLeakOpenProb profile (.firstLate secret)) *
          lateLeakSendValue profile payoff secret .secondIncluded .secondDropped := by
  rw [lateLeakFirstValue, lateLeakSecondValue, sends]
  ring

/-- A sequentially rational sender at the first late turn plays a strictly
preferred turn with probability one. -/
theorem lateLeak_rational_first_turn {A : (lateLeakModel true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates true) (lateLeakPayoff true))
    (secret : LateLeakType) :
    (lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) secret .secondIncluded
        .secondDropped <
      lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) secret .firstIncluded
        .firstDropped → lateLeakOpenProb A.strategy (.firstLate secret) = 1) ∧
    (lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) secret .firstIncluded
        .firstDropped <
      lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) secret .secondIncluded
        .secondDropped → lateLeakOpenProb A.strategy (.firstLate secret) = 0) := by
  have second := lateLeak_rational_second_sends rational secret
  let site := lateLeakSenderSite true (lateLeakFirstHistory secret) rfl
  have current : lateLeakValue A.strategy (lateLeakStatePayoff .sender) 5 (.firstLate secret) =
      lateLeakOpenProb A.strategy (.firstLate secret) *
          lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) secret .firstIncluded
            .firstDropped +
        (1 - lateLeakOpenProb A.strategy (.firstLate secret)) *
          lateLeakSendValue A.strategy (lateLeakStatePayoff .sender) secret .secondIncluded
            .secondDropped := by
    rw [show (5 : ℕ) = 2 + 3 from rfl, lateLeakValue_firstLate,
      lateLeakFirstValue_of_second_sends _ _ _ second]
  have sendFirst := lateLeak_sender_rational rational site (state := .firstLate secret) rfl
    (lateLeakCommitOpen (A.strategy .sender) (.firstLate secret) true ⟨true, rfl⟩)
  have holdFirst := lateLeak_sender_rational rational site (state := .firstLate secret) rfl
    (lateLeakCommitOpen (A.strategy .sender) (.firstLate secret) false ⟨false, rfl⟩)
  rw [current, show (5 : ℕ) = 2 + 3 from rfl, lateLeakValue_firstLate, lateLeakFirstValue,
    lateLeakOpenProb_update_commit_self, lateLeakSendValue_update_sender] at sendFirst holdFirst
  rw [lateLeakSecondValue, lateLeakOpenProb_update_commit_of_ne _ _ _ _ _ _
    (by simp), lateLeakUpdate_self, second, lateLeakSendValue_update_sender] at holdFirst
  simp only [ite_true, Bool.false_eq_true, ite_false, sub_self, zero_mul, add_zero, one_mul,
    sub_zero, zero_add] at sendFirst holdFirst
  have p0 := lateLeakOpenProb_nonneg A.strategy (.firstLate secret)
  have p1 := lateLeakOpenProb_le_one A.strategy (.firstLate secret)
  constructor
  · intro preferred
    nlinarith
  · intro preferred
    nlinarith

end Vegas
