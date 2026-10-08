/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLatePlay
import Vegas.Examples.LateLeak.Incentives

/-! # Incentives in the settle-late game

Every listener answer after an included opening pays the sender along one
direction, as in the late-turn game, so the sender's values are affine in the
listener's safe-answer and bit-guess probabilities. This file computes the
values of the inclusion step and bounds the packets that never pay: a raw
signal, a second opening after a first one, and never opening all cost the
sender at least `min c D` against the reward range, while the core packet
loses at most `(1 - q) (D + c)`. When `(1 - q) (D + c + R/2) < min c D - R/2`,
a sequentially rational sender therefore plays the core packet at the second
late turn after a silent protected turn, whatever the listener does and
whatever it believes about the leak.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : SettleLateParameters} {late : Bool}

/-! ## Laws -/

theorem settleLateSenderLaw_support (profile : SettleLateProfile G late) (view : SettleLateView)
    (choice : Option SettleLateMove)
    (supported : choice ∈ (settleLateSenderLaw profile view).support) :
    choice ∈ settleLateMenu late view := by
  rw [settleLateSenderLaw, PMF.mem_support_map_iff] at supported
  obtain ⟨option, _, rfl⟩ := supported
  exact option.2

theorem settleLateListenerLaw_support (profile : SettleLateProfile G late) (view : SettleLateView)
    (choice : Option SettleLateMove)
    (supported : choice ∈ (settleLateListenerLaw profile view).support) :
    choice ∈ settleLateMenu late view := by
  rw [settleLateListenerLaw, PMF.mem_support_map_iff] at supported
  obtain ⟨option, _, rfl⟩ := supported
  exact option.2

theorem settleLateSenderLaw_apply (profile : SettleLateProfile G late) (view : SettleLateView)
    (choice : Option SettleLateMove) (menu : choice ∈ settleLateMenu late view) :
    settleLateSenderLaw profile view choice = profile .sender view ⟨choice, menu⟩ :=
  pmf_map_apply_of_injective _ Subtype.val_injective
    (⟨choice, menu⟩ : (settleLateModel G late).Choice .sender view)

theorem settleLateListenerLaw_apply (profile : SettleLateProfile G late) (view : SettleLateView)
    (choice : Option SettleLateMove) (menu : choice ∈ settleLateMenu late view) :
    settleLateListenerLaw profile view choice = profile .listener view ⟨choice, menu⟩ :=
  pmf_map_apply_of_injective _ Subtype.val_injective
    (⟨choice, menu⟩ : (settleLateModel G late).Choice .listener view)

/-- The probability of the safe answer at a view. -/
def settleLateSafeProb (profile : SettleLateProfile G late) (view : SettleLateView) : ℝ :=
  (settleLateListenerLaw profile view (some (.reply .safe))).toReal

/-- The probability of the bit guess `1` at a view. -/
def settleLateBitOneProb (profile : SettleLateProfile G late) (view : SettleLateView) : ℝ :=
  (settleLateListenerLaw profile view (some (.reply (.failure true)))).toReal

/-- The probability that the listener emits its raw packet at a view. -/
def settleLatePingProb (profile : SettleLateProfile G late) (view : SettleLateView) : ℝ :=
  (settleLateListenerLaw profile view (some (.ping true))).toReal

theorem settleLateSafeProb_nonneg (profile : SettleLateProfile G late) (view : SettleLateView) :
    0 ≤ settleLateSafeProb profile view := ENNReal.toReal_nonneg

theorem settleLateSafeProb_le_one (profile : SettleLateProfile G late) (view : SettleLateView) :
    settleLateSafeProb profile view ≤ 1 := lateLeak_toReal_le_one _ _

theorem settleLateBitOneProb_nonneg (profile : SettleLateProfile G late) (view : SettleLateView) :
    0 ≤ settleLateBitOneProb profile view := ENNReal.toReal_nonneg

theorem settleLateBitOneProb_le_one (profile : SettleLateProfile G late) (view : SettleLateView) :
    settleLateBitOneProb profile view ≤ 1 := lateLeak_toReal_le_one _ _

theorem settleLatePingProb_nonneg (profile : SettleLateProfile G late) (view : SettleLateView) :
    0 ≤ settleLatePingProb profile view := ENNReal.toReal_nonneg

theorem settleLatePingProb_le_one (profile : SettleLateProfile G late) (view : SettleLateView) :
    settleLatePingProb profile view ≤ 1 := lateLeak_toReal_le_one _ _

/-- The observe-only activation averages over the listener's raw packet. -/
theorem settleLate_expect_ping (profile : SettleLateProfile G late) (early : Option Bool)
    (glimpse : SettleLateGlimpse) (value : Bool → ℝ) :
    expect (settleLateListenerLaw profile (.watching early glimpse))
        (fun choice => value (settleLatePingOf choice)) =
      settleLatePingProb profile (.watching early glimpse) * value true +
        (1 - settleLatePingProb profile (.watching early glimpse)) * value false := by
  rw [lateLeak_expect_two_point _ (some (.ping true)) _ (value false)]
  · rfl
  · intro choice supported different
    obtain ⟨sent, rfl⟩ := settleLateListenerLaw_support profile _ choice supported
    cases sent
    · rfl
    · exact (different rfl).elim

/-! ## Chance -/

theorem settleLateLeakCoin_true : (settleLateLeakCoin G true).toReal = settleLateLeakProb G := by
  simp only [settleLateLeakCoin, PMF.ofFintype_apply, ite_true]
  exact ENNReal.toReal_ofReal (settleLateLeakProb_pos G).le

theorem settleLateLeakCoin_false :
    (settleLateLeakCoin G false).toReal = 1 - settleLateLeakProb G := by
  simp only [settleLateLeakCoin, PMF.ofFintype_apply, Bool.false_eq_true, ite_false]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (settleLateLeakProb_lt_one G).le)

theorem settleLateLeakCoin_ne_zero (seen : Bool) : settleLateLeakCoin G seen ≠ 0 := by
  have l0 := settleLateLeakProb_pos G
  have l1 := settleLateLeakProb_lt_one G
  cases seen <;> simp [settleLateLeakCoin, PMF.ofFintype_apply, l0, l1]

theorem settleLate_expect_leakCoin (g : Bool → ℝ) :
    expect (settleLateLeakCoin G) g =
      settleLateLeakProb G * g true + (1 - settleLateLeakProb G) * g false := by
  rw [expect_eq_sum, Fintype.sum_bool, settleLateLeakCoin_true, settleLateLeakCoin_false]

/-- After a first-turn opening the observe-only activation saw, the sender
holding at the second turn faces one inclusion coin. -/
theorem settleLate_expect_fate_seenHold (g : SettleLateFate → ℝ) :
    expect (settleLateFateLaw G (.opening true) .silent) g =
      lateLeakInclusionProb G.toLateLeakParameters * g ⟨some .first, false, false⟩ +
        (1 - lateLeakInclusionProb G.toLateLeakParameters) * g ⟨none, false, false⟩ := by
  simp only [settleLateFateLaw, SettleLateFirst.opened, SettleLatePacket.isOpening,
    SettleLateFirst.seen]
  rw [expect_bind_of_finite, lateLeak_expect_inclusion]
  simp [settleLateExposure, expect_pure, expect_map]

/-- After a first-turn opening it did not see, the listener may still see the
dropped opening when it answers. -/
theorem settleLate_expect_fate_unseenHold (g : SettleLateFate → ℝ) :
    expect (settleLateFateLaw G (.opening false) .silent) g =
      lateLeakInclusionProb G.toLateLeakParameters * g ⟨some .first, false, false⟩ +
        (1 - lateLeakInclusionProb G.toLateLeakParameters) *
          (settleLateLeakProb G * g ⟨none, true, false⟩ +
            (1 - settleLateLeakProb G) * g ⟨none, false, false⟩) := by
  simp only [settleLateFateLaw, SettleLateFirst.opened, SettleLatePacket.isOpening,
    SettleLateFirst.seen]
  rw [expect_bind_of_finite, lateLeak_expect_inclusion]
  simp only [ite_true, Bool.false_eq_true, ite_false, expect_pure, settleLateExposure,
    Bool.not_false, expect_map, Function.comp_def, settleLate_expect_leakCoin]

/-- A sole opening at the second late turn. -/
theorem settleLate_expect_fate_send (g : SettleLateFate → ℝ) :
    expect (settleLateFateLaw G .silent .opening) g =
      lateLeakInclusionProb G.toLateLeakParameters * g ⟨some .second, false, false⟩ +
        (1 - lateLeakInclusionProb G.toLateLeakParameters) *
          (settleLateLeakProb G * g ⟨none, false, true⟩ +
            (1 - settleLateLeakProb G) * g ⟨none, false, false⟩) := by
  simp only [settleLateFateLaw, SettleLateFirst.opened, SettleLatePacket.isOpening]
  rw [expect_bind_of_finite, lateLeak_expect_inclusion]
  simp only [ite_true, Bool.false_eq_true, ite_false, expect_pure, expect_map, Function.comp_def,
    settleLate_expect_leakCoin]

/-- Without a late opening the reveal fails surely. -/
theorem settleLateFateLaw_closed {first : SettleLateFirst} {second : SettleLatePacket}
    (firstClosed : first.opened = false) (secondClosed : second.isOpening = false) :
    settleLateFateLaw G first second = PMF.pure ⟨none, false, false⟩ := by
  simp only [settleLateFateLaw, firstClosed, secondClosed]

/-! ## Answer values -/

theorem settleLateReport_success (record : SettleLateRecord) :
    record.report.included.isSome = record.succeeded := by
  simp [SettleLateRecord.report, SettleLateRecord.succeeded]

/-- The sender's value of an answer after an included opening. -/
theorem settleLateAnswerValue_success (profile : SettleLateProfile G late)
    (record : SettleLateRecord) (succeeded : record.succeeded = true) :
    settleLateAnswerValue profile (settleLateStatePayoff G .sender) record =
      settleLateSafeProb profile (.asked record.report) * (G.reward / 2) +
        (1 - settleLateSafeProb profile (.asked record.report)) *
          lateLeakGuessGain G.toLateLeakParameters record.secret.2 -
        (if record.charged then G.dropCharge else 0) := by
  rw [settleLateAnswerValue, lateLeak_expect_two_point _ (some (.reply .safe)) _
    (lateLeakGuessGain G.toLateLeakParameters record.secret.2 -
      (if record.charged then G.dropCharge else 0))]
  · simp only [settleLateReplyOf, settleLateStatePayoff, settleLateSenderBase, succeeded,
      ite_true, sub_zero, settleLateSafeProb]
    ring
  · intro choice supported different
    obtain ⟨answer, rfl, fits⟩ := settleLateListenerLaw_support profile _ choice supported
    rw [settleLateReport_success, succeeded] at fits
    cases answer with
    | safe => exact (different rfl).elim
    | guess label =>
        simp [settleLateReplyOf, settleLateStatePayoff, settleLateSenderBase, succeeded,
          lateLeakGuessGain]
    | failure bit => simp [LateLeakAnswer.fitsOutcome] at fits

/-- The sender's value of an answer after a failed reveal. -/
theorem settleLateAnswerValue_failure (profile : SettleLateProfile G late)
    (record : SettleLateRecord) (failed : record.succeeded = false) :
    settleLateAnswerValue profile (settleLateStatePayoff G .sender) record =
      settleLateBitOneProb profile (.asked record.report) *
          lateLeakBitOneGain G.toLateLeakParameters record.secret.2 +
        (1 - settleLateBitOneProb profile (.asked record.report)) *
          lateLeakBitZeroGain G.toLateLeakParameters record.secret.2 - G.forfeit -
        (if record.charged then G.dropCharge else 0) := by
  rw [settleLateAnswerValue, lateLeak_expect_two_point _ (some (.reply (.failure true))) _
    (lateLeakBitZeroGain G.toLateLeakParameters record.secret.2 - G.forfeit -
      (if record.charged then G.dropCharge else 0))]
  · cases label : record.secret.2 <;>
      simp [settleLateReplyOf, settleLateStatePayoff, settleLateSenderBase, failed,
        settleLateBitOneProb, lateLeakBitOneGain, lateLeakBitZeroGain, label] <;> ring
  · intro choice supported different
    obtain ⟨answer, rfl, fits⟩ := settleLateListenerLaw_support profile _ choice supported
    rw [settleLateReport_success, failed] at fits
    cases answer with
    | failure bit =>
        cases bit
        · cases label : record.secret.2 <;>
            simp [settleLateReplyOf, settleLateStatePayoff, settleLateSenderBase, failed,
              lateLeakBitZeroGain, label]
        · exact (different rfl).elim
    | _ => simp [LateLeakAnswer.fitsOutcome] at fits

/-- Answer values depend on a record only through what the listener sees, the
type, and whether the reveal succeeded and the escrow charges. -/
theorem settleLateAnswerValue_congr (profile : SettleLateProfile G late)
    {record other : SettleLateRecord} (report : record.report = other.report)
    (secret : record.secret = other.secret) (succeeded : record.succeeded = other.succeeded)
    (charged : record.charged = other.charged) :
    settleLateAnswerValue profile (settleLateStatePayoff G .sender) record =
      settleLateAnswerValue profile (settleLateStatePayoff G .sender) other := by
  simp only [settleLateAnswerValue, settleLateStatePayoff, report, secret, succeeded, charged]

/-! ## Bounds -/

/-- The largest payoff an answer can give a label. -/
def settleLateTop (G : SettleLateParameters) (label : LateLeakLabel) : ℝ :=
  if label = .c then G.reward / 2 else G.reward

/-- The smallest payoff an answer after an included opening can give a label. -/
def settleLateFloor (G : SettleLateParameters) (label : LateLeakLabel) : ℝ :=
  if label = .c then 0 else G.reward / 2

theorem settleLateTop_sub_floor (label : LateLeakLabel) :
    settleLateTop G label - settleLateFloor G label = G.reward / 2 := by
  cases label <;> simp only [settleLateTop, settleLateFloor, reduceCtorEq, ite_true,
    ite_false] <;> ring

theorem settleLateFloor_nonneg (R0 : 0 ≤ G.reward) (label : LateLeakLabel) :
    0 ≤ settleLateFloor G label := by
  cases label <;> simp only [settleLateFloor, reduceCtorEq, ite_true, ite_false] <;> linarith

theorem settleLateFloor_le (R0 : 0 ≤ G.reward) (label : LateLeakLabel) :
    settleLateFloor G label ≤ G.reward / 2 := by
  cases label <;> simp only [settleLateFloor, reduceCtorEq, ite_true, ite_false] <;> linarith

theorem settleLateSenderBase_le (R0 : 0 ≤ G.reward) (label : LateLeakLabel) (succeeded : Bool)
    (answer : LateLeakAnswer) :
    settleLateSenderBase G label succeeded answer ≤ settleLateTop G label := by
  have zero : (0 : ℝ) ≤ G.reward / 2 := by linarith
  rcases answer with _ | guessed | bit
  · cases label <;> cases succeeded <;> simp [settleLateSenderBase, settleLateTop, zero, R0]
  · cases label <;> cases succeeded <;> simp [settleLateSenderBase, settleLateTop, zero, R0]
  · cases label <;> cases succeeded <;> cases bit <;>
      simp [settleLateSenderBase, settleLateTop, zero, R0]

/-- Every answer value is at most the label's largest payoff, less the forfeit
and the charge it carries. -/
theorem settleLateAnswerValue_le (profile : SettleLateProfile G late) (R0 : 0 ≤ G.reward)
    (record : SettleLateRecord) :
    settleLateAnswerValue profile (settleLateStatePayoff G .sender) record ≤
      settleLateTop G record.secret.2 - (if record.succeeded then 0 else G.forfeit) -
        (if record.charged then G.dropCharge else 0) := by
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
  intro choice _
  simp only [settleLateStatePayoff]
  linarith [settleLateSenderBase_le R0 record.secret.2 record.succeeded (settleLateReplyOf choice)]

/-- An uncharged included opening gives a label at least its smallest
payoff. -/
theorem settleLateAnswerValue_success_ge (profile : SettleLateProfile G late) (R0 : 0 ≤ G.reward)
    (record : SettleLateRecord) (succeeded : record.succeeded = true)
    (uncharged : record.charged = false) :
    settleLateFloor G record.secret.2 ≤
      settleLateAnswerValue profile (settleLateStatePayoff G .sender) record := by
  rw [settleLateAnswerValue_success profile record succeeded, uncharged]
  have m0 := settleLateSafeProb_nonneg profile (.asked record.report)
  have m1 := settleLateSafeProb_le_one profile (.asked record.report)
  cases label : record.secret.2 <;>
    simp only [settleLateFloor, lateLeakGuessGain, reduceCtorEq, ite_true, ite_false,
      Bool.false_eq_true, sub_zero] <;> nlinarith

/-- A failed reveal costs at most the forfeit and the charge. -/
theorem settleLateAnswerValue_failure_ge (profile : SettleLateProfile G late) (R0 : 0 ≤ G.reward)
    (c0 : 0 ≤ G.dropCharge) (record : SettleLateRecord) (failed : record.succeeded = false) :
    -G.forfeit - G.dropCharge ≤
      settleLateAnswerValue profile (settleLateStatePayoff G .sender) record := by
  rw [settleLateAnswerValue_failure profile record failed]
  have b0 := settleLateBitOneProb_nonneg profile (.asked record.report)
  have b1 := settleLateBitOneProb_le_one profile (.asked record.report)
  have one0 : 0 ≤ lateLeakBitOneGain G.toLateLeakParameters record.secret.2 := by
    unfold lateLeakBitOneGain
    split <;> linarith
  have zero0 : 0 ≤ lateLeakBitZeroGain G.toLateLeakParameters record.secret.2 := by
    unfold lateLeakBitZeroGain
    split <;> linarith
  have charge : (if record.charged then G.dropCharge else 0) ≤ G.dropCharge := by
    split <;> linarith
  nlinarith [mul_nonneg b0 one0, mul_nonneg (sub_nonneg.mpr b1) zero0]

/-! ## The core packet -/

/-- The packet that a sender who has deferred plays at the second late turn:
hold after a first-turn opening, open otherwise. -/
def settleLateCorePacket : SettleLatePacket → SettleLatePacket
  | .opening => .silent
  | _ => .opening

/-- A first late turn that sent no raw signal. -/
def SettleLateFirst.Plain (first : SettleLateFirst) : Prop :=
  first = .silent ∨ ∃ seen, first = .opening seen

/-- The core packet loses at most `(1 - q) (D + c)` below the label's smallest
payoff after an inclusion, whatever the listener does. -/
theorem settleLateSettleValue_core_ge (profile : SettleLateProfile G late) (R0 : 0 ≤ G.reward)
    (c0 : 0 ≤ G.dropCharge) (secret : LateLeakType) {first : SettleLateFirst}
    (plain : first.Plain) (ping : Bool) :
    lateLeakInclusionProb G.toLateLeakParameters * settleLateFloor G secret.2 -
        (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
      settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none first ping
        (settleLateCorePacket first.packet) := by
  have q0 := (lateLeakInclusionProb_pos G.toLateLeakParameters).le
  have q1 := sub_nonneg.mpr (lateLeakInclusionProb_lt_one G.toLateLeakParameters).le
  have l0 := (settleLateLeakProb_pos G).le
  have l1 := sub_nonneg.mpr (settleLateLeakProb_lt_one G).le
  have fail (record : SettleLateRecord) (failed : record.succeeded = false) :=
    settleLateAnswerValue_failure_ge profile R0 c0 record failed
  have win (record : SettleLateRecord) (succeeded : record.succeeded = true)
      (uncharged : record.charged = false) :=
    settleLateAnswerValue_success_ge profile R0 record succeeded uncharged
  have mixed {x y : ℝ} (hx : -G.forfeit - G.dropCharge ≤ x) (hy : -G.forfeit - G.dropCharge ≤ y) :
      -(G.forfeit + G.dropCharge) ≤ settleLateLeakProb G * x + (1 - settleLateLeakProb G) * y := by
    nlinarith [mul_le_mul_of_nonneg_left hx l0, mul_le_mul_of_nonneg_left hy l1]
  rcases plain with rfl | ⟨seen, rfl⟩
  · rw [settleLateSettleValue, show settleLateCorePacket SettleLateFirst.silent.packet = .opening
      from rfl, settleLate_expect_fate_send]
    have s := win ⟨secret, none, .silent, ping, .opening, ⟨some .second, false, false⟩⟩ rfl rfl
    have f1 := fail ⟨secret, none, .silent, ping, .opening, ⟨none, false, true⟩⟩ rfl
    have f2 := fail ⟨secret, none, .silent, ping, .opening, ⟨none, false, false⟩⟩ rfl
    simp only at s f1 f2
    have mix := mixed f1 f2
    nlinarith [mul_le_mul_of_nonneg_left s q0, mul_le_mul_of_nonneg_left mix q1]
  · cases seen
    · rw [settleLateSettleValue, show settleLateCorePacket (SettleLateFirst.opening false).packet =
        .silent from rfl, settleLate_expect_fate_unseenHold]
      have s := win ⟨secret, none, .opening false, ping, .silent, ⟨some .first, false, false⟩⟩
        rfl rfl
      have f1 := fail ⟨secret, none, .opening false, ping, .silent, ⟨none, true, false⟩⟩ rfl
      have f2 := fail ⟨secret, none, .opening false, ping, .silent, ⟨none, false, false⟩⟩ rfl
      simp only at s f1 f2
      have mix := mixed f1 f2
      nlinarith [mul_le_mul_of_nonneg_left s q0, mul_le_mul_of_nonneg_left mix q1]
    · rw [settleLateSettleValue, show settleLateCorePacket (SettleLateFirst.opening true).packet =
        .silent from rfl, settleLate_expect_fate_seenHold]
      have s := win ⟨secret, none, .opening true, ping, .silent, ⟨some .first, false, false⟩⟩
        rfl rfl
      have f := fail ⟨secret, none, .opening true, ping, .silent, ⟨none, false, false⟩⟩ rfl
      simp only at s f
      nlinarith [mul_le_mul_of_nonneg_left s q0, mul_le_mul_of_nonneg_left f q1]

/-- Every other packet at the second late turn costs the sender at least
`min c D` below the label's largest payoff: a raw signal and a second opening
are charged surely, and never opening forfeits surely. -/
theorem settleLateSettleValue_extra_le (profile : SettleLateProfile G late) (R0 : 0 ≤ G.reward)
    (D0 : 0 ≤ G.forfeit) (secret : LateLeakType)
    {first : SettleLateFirst} (plain : first.Plain) (ping : Bool) (second : SettleLatePacket)
    (extra : second ≠ settleLateCorePacket first.packet) :
    settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none first ping second ≤
      settleLateTop G secret.2 - min G.dropCharge G.forfeit := by
  have bound (record : SettleLateRecord) := settleLateAnswerValue_le profile R0 record
  have minC := min_le_left G.dropCharge G.forfeit
  have minD := min_le_right G.dropCharge G.forfeit
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
  intro fate supported
  have value := bound ⟨secret, none, first, ping, second, fate⟩
  have charged_bound (charged : (⟨secret, none, first, ping, second, fate⟩ :
      SettleLateRecord).charged = true) :
      settleLateAnswerValue profile (settleLateStatePayoff G .sender)
        ⟨secret, none, first, ping, second, fate⟩ ≤
      settleLateTop G secret.2 - min G.dropCharge G.forfeit := by
    rw [charged] at value
    simp only [ite_true] at value
    split at value <;> linarith
  cases second with
  | signal word =>
      exact charged_bound (by simp [SettleLateRecord.charged, SettleLatePacket.isSignal])
  | opening =>
      rcases plain with rfl | ⟨seen, rfl⟩
      · exact (extra rfl).elim
      · apply charged_bound
        simp only [SettleLateRecord.charged, SettleLateRecord.dropped, SettleLateFirst.opened,
          SettleLatePacket.isOpening, Bool.true_and, Bool.or_eq_true]
        right
        cases included : fate.included with
        | none => simp
        | some slot => cases slot <;> simp
  | silent =>
      rcases plain with rfl | ⟨seen, rfl⟩
      · rw [settleLateFateLaw_closed rfl rfl, PMF.mem_support_pure_iff] at supported
        subst supported
        simp only [SettleLateRecord.succeeded, Option.isSome_none, Bool.false_eq_true,
          ite_false] at value
        split at value <;> linarith
      · exact (extra rfl).elim

/-! ## Rational play -/

/-- A law at which a dominant option is at least as good as the law itself puts
probability one on that option. -/
theorem pmf_apply_eq_one_of_dominant {ι α : Type*} [Finite α] (belief : PMF ι) [Finite ι]
    (law : PMF α) (value : ι → α → ℝ) (best : α) {δ : ℝ} (positive : 0 < δ)
    (gap : ∀ i, ∀ x ∈ law.support, x ≠ best → value i x + δ ≤ value i best)
    (rational : expect belief (fun i => value i best) ≤
      expect belief (fun i => expect law (value i))) :
    law best = 1 := by
  classical
  have each (i : ι) : expect law (value i) ≤
      value i best - δ * (1 - (law best).toReal) := by
    have split := lateLeak_expect_two_point law best
      (fun x => if x = best then value i best else value i best - δ) (value i best - δ)
      (fun x _ different => by simp [different])
    simp only [ite_true] at split
    have mono : expect law (value i) ≤
        expect law (fun x => if x = best then value i best else value i best - δ) := by
      apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
      intro x supported
      by_cases same : x = best
      · subst same
        simp
      · simp only [same, ite_false]
        linarith [gap i x supported same]
    rw [split] at mono
    linarith
  have total : expect belief (fun i => expect law (value i)) ≤
      expect belief (fun i => value i best) - δ * (1 - (law best).toReal) := by
    have shifted := expect_mono (μ := belief) (fun i _ => each i)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
      expect_constant] at shifted
    exact shifted
  have mass := lateLeak_toReal_le_one law best
  have one : (law best).toReal = 1 := by
    by_contra different
    have below : (law best).toReal < 1 := lt_of_le_of_ne mass different
    nlinarith
  exact (ENNReal.toReal_eq_one_iff _).mp one

/-- A dominant option at one state's law has probability one. -/
theorem pmf_apply_eq_one_of_dominant_at {α : Type*} [Finite α] (law : PMF α)
    (value : α → ℝ)
    (best : α) {δ : ℝ} (positive : 0 < δ)
    (gap : ∀ x ∈ law.support, x ≠ best → value x + δ ≤ value best)
    (rational : value best ≤ expect law value) : law best = 1 :=
  pmf_apply_eq_one_of_dominant (PMF.pure ()) law (fun _ => value) best positive (fun _ => gap)
    (by simpa only [expect_pure] using rational)

theorem settleLate_law_eq_pure {α : Type*} {law : PMF α} {best : α} (one : law best = 1) :
    law = PMF.pure best :=
  pmf_eq_pure_of_support_subset_singleton law best ((PMF.apply_eq_one_iff law best).mp one).le

end Vegas
