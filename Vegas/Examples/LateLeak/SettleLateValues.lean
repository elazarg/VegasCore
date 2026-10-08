/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateTurns
import Vegas.Examples.LateLeak.SettleLateListener
import Vegas.Examples.LateLeak.Impossibility

/-! # Values of deferring in the settle-late game

A sender who deferred silently and plays the core packet at the second late
turn reaches five kinds of answers:

* after an opening the observe-only activation saw: an inclusion, where the
  listener knows it saw the opening before the second turn, or a failure with
  the bit known;
* after an opening it did not see, or an opening at the second turn: an
  inclusion of serial zero, a failure whose dropped opening the listener sees
  when it answers, or a failure with the bit unknown.

The two second kinds of answer are the same for both late turns. Opening at the
first late turn therefore differs from holding only through what the leak
showed before the second turn, which happens with probability `λ`: the
difference is `λ` times the late-turn game's label preference, with the leak
pull scaled by `1 - λ`. Whatever the listener answers after an unseen failure,
the leak pull is nonzero in some class of the committed bit, so two types of
that class strictly prefer opposite late turns.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : SettleLateParameters} {late : Bool}

/-! ## Reports along the core plans -/

/-- What the listener sees when the observe-only activation saw the
first-turn opening: the bit, its own raw packet, and the inclusion. -/
def settleLateSeenReport (bit ping : Bool) (included : Option ℕ) : SettleLateReport where
  early := none
  glimpse := .opening bit
  ping := ping
  included := included
  exposed := []
  talk := none
  bit := some bit

/-- What the listener sees when the observe-only activation saw no opening. -/
def settleLateQuietReport (ping : Bool) (included : Option ℕ) (exposed : List ℕ)
    (bit : Option Bool) : SettleLateReport where
  early := none
  glimpse := .nothing
  ping := ping
  included := included
  exposed := exposed
  talk := none
  bit := bit

/-- The sender's value of an answer after an inclusion, given the safe-answer
probability. -/
def settleLateSuccessValue (G : SettleLateParameters) (safe : ℝ) (label : LateLeakLabel) : ℝ :=
  safe * (G.reward / 2) + (1 - safe) * lateLeakGuessGain G.toLateLeakParameters label

/-- The sender's value of an answer after a failure, before the forfeit and the
charge, given the probability of the bit guess `1`. -/
def settleLateFailureValue (G : SettleLateParameters) (bitOne : ℝ) (label : LateLeakLabel) : ℝ :=
  bitOne * lateLeakBitOneGain G.toLateLeakParameters label +
    (1 - bitOne) * lateLeakBitZeroGain G.toLateLeakParameters label

theorem settleLateFailureValue_nonneg (R0 : 0 ≤ G.reward) {bitOne : ℝ} (b0 : 0 ≤ bitOne)
    (b1 : bitOne ≤ 1) (label : LateLeakLabel) : 0 ≤ settleLateFailureValue G bitOne label := by
  have one : 0 ≤ lateLeakBitOneGain G.toLateLeakParameters label := by
    unfold lateLeakBitOneGain
    split <;> linarith
  have zero : 0 ≤ lateLeakBitZeroGain G.toLateLeakParameters label := by
    unfold lateLeakBitZeroGain
    split <;> linarith
  unfold settleLateFailureValue
  nlinarith [mul_nonneg b0 one, mul_nonneg (sub_nonneg.mpr b1) zero]

theorem settleLateSuccessValue_label_a_ge (R0 : 0 ≤ G.reward) {safe : ℝ}
    (s1 : safe ≤ 1) : G.reward / 2 ≤ settleLateSuccessValue G safe .a := by
  simp only [settleLateSuccessValue, lateLeakGuessGain, reduceCtorEq, ite_false]
  nlinarith

/-! ## The inclusion step along the core plans -/

/-- Holding after a first-turn opening the observe-only activation saw. -/
theorem settleLateSettleValue_seenHold (profile : SettleLateProfile G late)
    (secret : LateLeakType) (ping : Bool) :
    settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none (.opening true)
        ping .silent =
      lateLeakInclusionProb G.toLateLeakParameters * settleLateSuccessValue G
          (settleLateSafeProb profile (.asked (settleLateSeenReport secret.1 ping (some 0))))
          secret.2 +
        (1 - lateLeakInclusionProb G.toLateLeakParameters) *
          (settleLateFailureValue G
            (settleLateBitOneProb profile (.asked (settleLateSeenReport secret.1 ping none)))
            secret.2 - G.forfeit - G.dropCharge) := by
  rw [settleLateSettleValue, settleLate_expect_fate_seenHold, settleLateAnswerValue_success _ _ rfl,
    settleLateAnswerValue_failure _ _ rfl]
  have success : (⟨secret, none, .opening true, ping, .silent, ⟨some .first, false, false⟩⟩ :
      SettleLateRecord).report = settleLateSeenReport secret.1 ping (some 0) := rfl
  have failure : (⟨secret, none, .opening true, ping, .silent, ⟨none, false, false⟩⟩ :
      SettleLateRecord).report = settleLateSeenReport secret.1 ping none := rfl
  have quiet : (⟨secret, none, .opening true, ping, .silent, ⟨some .first, false, false⟩⟩ :
      SettleLateRecord).charged = false := rfl
  have dropped : (⟨secret, none, .opening true, ping, .silent, ⟨none, false, false⟩⟩ :
      SettleLateRecord).charged = true := rfl
  simp only [success, failure, quiet, dropped, Bool.false_eq_true, ite_false, ite_true, sub_zero,
    settleLateSuccessValue, settleLateFailureValue]

/-- Holding after a first-turn opening the observe-only activation missed. -/
theorem settleLateSettleValue_unseenHold (profile : SettleLateProfile G late)
    (secret : LateLeakType) (ping : Bool) :
    settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none (.opening false)
        ping .silent =
      lateLeakInclusionProb G.toLateLeakParameters * settleLateSuccessValue G
          (settleLateSafeProb profile (.asked (settleLateQuietReport ping (some 0) []
            (some secret.1)))) secret.2 +
        (1 - lateLeakInclusionProb G.toLateLeakParameters) *
          (settleLateLeakProb G * (settleLateFailureValue G
              (settleLateBitOneProb profile (.asked (settleLateQuietReport ping none [0]
                (some secret.1)))) secret.2 - G.forfeit - G.dropCharge) +
            (1 - settleLateLeakProb G) * (settleLateFailureValue G
              (settleLateBitOneProb profile (.asked (settleLateQuietReport ping none [] none)))
              secret.2 - G.forfeit - G.dropCharge)) := by
  rw [settleLateSettleValue, settleLate_expect_fate_unseenHold,
    settleLateAnswerValue_success _ _ rfl, settleLateAnswerValue_failure _ _ rfl,
    settleLateAnswerValue_failure _ _ rfl]
  have success : (⟨secret, none, .opening false, ping, .silent, ⟨some .first, false, false⟩⟩ :
      SettleLateRecord).report = settleLateQuietReport ping (some 0) [] (some secret.1) := rfl
  have exposed : (⟨secret, none, .opening false, ping, .silent, ⟨none, true, false⟩⟩ :
      SettleLateRecord).report = settleLateQuietReport ping none [0] (some secret.1) := rfl
  have unknown : (⟨secret, none, .opening false, ping, .silent, ⟨none, false, false⟩⟩ :
      SettleLateRecord).report = settleLateQuietReport ping none [] none := rfl
  have quiet : (⟨secret, none, .opening false, ping, .silent, ⟨some .first, false, false⟩⟩ :
      SettleLateRecord).charged = false := rfl
  have dropped₁ : (⟨secret, none, .opening false, ping, .silent, ⟨none, true, false⟩⟩ :
      SettleLateRecord).charged = true := rfl
  have dropped₂ : (⟨secret, none, .opening false, ping, .silent, ⟨none, false, false⟩⟩ :
      SettleLateRecord).charged = true := rfl
  simp only [success, exposed, unknown, quiet, dropped₁, dropped₂, Bool.false_eq_true, ite_false,
    ite_true, sub_zero, settleLateSuccessValue, settleLateFailureValue]

/-- Opening at the second late turn after holding at the first. -/
theorem settleLateSettleValue_send (profile : SettleLateProfile G late)
    (secret : LateLeakType) (ping : Bool) :
    settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none .silent ping
        .opening =
      settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none (.opening false)
        ping .silent := by
  rw [settleLateSettleValue_unseenHold, settleLateSettleValue, settleLate_expect_fate_send,
    settleLateAnswerValue_success _ _ rfl, settleLateAnswerValue_failure _ _ rfl,
    settleLateAnswerValue_failure _ _ rfl]
  have success : (⟨secret, none, .silent, ping, .opening, ⟨some .second, false, false⟩⟩ :
      SettleLateRecord).report = settleLateQuietReport ping (some 0) [] (some secret.1) := rfl
  have exposed : (⟨secret, none, .silent, ping, .opening, ⟨none, false, true⟩⟩ :
      SettleLateRecord).report = settleLateQuietReport ping none [0] (some secret.1) := rfl
  have unknown : (⟨secret, none, .silent, ping, .opening, ⟨none, false, false⟩⟩ :
      SettleLateRecord).report = settleLateQuietReport ping none [] none := rfl
  have quiet : (⟨secret, none, .silent, ping, .opening, ⟨some .second, false, false⟩⟩ :
      SettleLateRecord).charged = false := rfl
  have dropped₁ : (⟨secret, none, .silent, ping, .opening, ⟨none, false, true⟩⟩ :
      SettleLateRecord).charged = true := rfl
  have dropped₂ : (⟨secret, none, .silent, ping, .opening, ⟨none, false, false⟩⟩ :
      SettleLateRecord).charged = true := rfl
  simp only [success, exposed, unknown, quiet, dropped₁, dropped₂, Bool.false_eq_true, ite_false,
    ite_true, sub_zero, settleLateSuccessValue, settleLateFailureValue]

/-! ## Values along the late turns -/

theorem settleLateSecondValue_of_law (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (early : Option Bool)
    (first : SettleLateFirst) (ping : Bool) (packet : SettleLatePacket)
    (law : settleLateSenderLaw profile (.secondTurn secret early first.packet ping) =
      PMF.pure (some (.emit packet))) :
    settleLateSecondValue profile payoff secret early first ping =
      settleLateSettleValue profile payoff secret early first ping packet := by
  rw [settleLateSecondValue, law, expect_pure]
  rfl

theorem settleLateWatchValue_eq (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (early : Option Bool)
    (first : SettleLateFirst) :
    settleLateWatchValue profile payoff secret early first =
      settleLatePingProb profile (.watching early (first.glimpse secret.1)) *
          settleLateSecondValue profile payoff secret early first true +
        (1 - settleLatePingProb profile (.watching early (first.glimpse secret.1))) *
          settleLateSecondValue profile payoff secret early first false :=
  settleLate_expect_ping profile early _ _

theorem settleLateEmitValue_opening (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (early : Option Bool) :
    settleLateEmitValue profile payoff secret early .opening =
      settleLateLeakProb G * settleLateWatchValue profile payoff secret early (.opening true) +
        (1 - settleLateLeakProb G) *
          settleLateWatchValue profile payoff secret early (.opening false) := by
  rw [settleLateEmitValue, settleLateFirstLaw, expect_map]
  exact settleLate_expect_leakCoin _

theorem settleLateEmitValue_signal (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (early : Option Bool) (word : Bool) :
    settleLateEmitValue profile payoff secret early (.signal word) =
      settleLateWatchValue profile payoff secret early (.signal word) := by
  rw [settleLateEmitValue, settleLateFirstLaw, expect_pure]

theorem settleLateEmitValue_silent (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (early : Option Bool) :
    settleLateEmitValue profile payoff secret early .silent =
      settleLateWatchValue profile payoff secret early .silent := by
  rw [settleLateEmitValue, settleLateFirstLaw, expect_pure]

/-- The sender of a type plays the core packet at its second late turns after a
silent protected turn. -/
def SettleLateCorePlay (profile : SettleLateProfile G late) (secret : LateLeakType) : Prop :=
  ∀ ping, settleLateSenderLaw profile (.secondTurn secret none .silent ping) =
      PMF.pure (some (.emit .opening)) ∧
    settleLateSenderLaw profile (.secondTurn secret none .opening ping) =
      PMF.pure (some (.emit .silent))

theorem settleLate_rational_corePlay (pays : G.DeferralPays)
    {A : (settleLateModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G true) (settleLatePayoff G true))
    (secret : LateLeakType) : SettleLateCorePlay A.strategy secret := fun ping =>
  ⟨settleLate_rational_second_core pays rational secret (first := .silent) (Or.inl rfl) ping,
    settleLate_rational_second_core pays rational secret (first := .opening true)
      (Or.inr ⟨true, rfl⟩) ping⟩

/-- The value of holding at the first late turn under core play. -/
theorem settleLateEmitValue_silent_core (profile : SettleLateProfile G late)
    (secret : LateLeakType) (core : SettleLateCorePlay profile secret) :
    settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none .silent =
      settleLatePingProb profile (.watching none .nothing) *
          settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none
            (.opening false) true .silent +
        (1 - settleLatePingProb profile (.watching none .nothing)) *
          settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none
            (.opening false) false .silent := by
  rw [settleLateEmitValue_silent, settleLateWatchValue_eq,
    settleLateSecondValue_of_law _ _ _ _ _ _ _ (core true).1,
    settleLateSecondValue_of_law _ _ _ _ _ _ _ (core false).1,
    settleLateSettleValue_send, settleLateSettleValue_send]
  rfl

/-- The value of opening at the first late turn under core play. -/
theorem settleLateEmitValue_opening_core (profile : SettleLateProfile G late)
    (secret : LateLeakType) (core : SettleLateCorePlay profile secret) :
    settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none .opening =
      settleLateLeakProb G *
          (settleLatePingProb profile (.watching none (.opening secret.1)) *
              settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none
                (.opening true) true .silent +
            (1 - settleLatePingProb profile (.watching none (.opening secret.1))) *
              settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none
                (.opening true) false .silent) +
        (1 - settleLateLeakProb G) *
          settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none .silent := by
  rw [settleLateEmitValue_opening, settleLateEmitValue_silent_core profile secret core,
    settleLateWatchValue_eq, settleLateWatchValue_eq,
    settleLateSecondValue_of_law _ _ _ _ (.opening true) _ _ (core true).2,
    settleLateSecondValue_of_law _ _ _ _ (.opening true) _ _ (core false).2,
    settleLateSecondValue_of_law _ _ _ _ (.opening false) _ _ (core true).2,
    settleLateSecondValue_of_law _ _ _ _ (.opening false) _ _ (core false).2]
  rfl

/-! ## The first-turn preference -/

/-- The listener's averaged safe-answer probability after a first-turn
inclusion it saw pending. -/
def settleLateSeenSafe (profile : SettleLateProfile G late) (bit : Bool) : ℝ :=
  settleLatePingProb profile (.watching none (.opening bit)) *
      settleLateSafeProb profile (.asked (settleLateSeenReport bit true (some 0))) +
    (1 - settleLatePingProb profile (.watching none (.opening bit))) *
      settleLateSafeProb profile (.asked (settleLateSeenReport bit false (some 0)))

/-- The listener's averaged safe-answer probability after an inclusion of
serial zero it did not see pending. -/
def settleLateQuietSafe (profile : SettleLateProfile G late) (bit : Bool) : ℝ :=
  settleLatePingProb profile (.watching none .nothing) *
      settleLateSafeProb profile (.asked (settleLateQuietReport true (some 0) [] (some bit))) +
    (1 - settleLatePingProb profile (.watching none .nothing)) *
      settleLateSafeProb profile (.asked (settleLateQuietReport false (some 0) [] (some bit)))

/-- The listener's averaged probability of the bit guess `1` after a failure
in which it never saw the bit. -/
def settleLateQuietBitOne (profile : SettleLateProfile G late) : ℝ :=
  settleLatePingProb profile (.watching none .nothing) *
      settleLateBitOneProb profile (.asked (settleLateQuietReport true none [] none)) +
    (1 - settleLatePingProb profile (.watching none .nothing)) *
      settleLateBitOneProb profile (.asked (settleLateQuietReport false none [] none))

/-- The pull of the leak after a failure in one class of the committed bit. -/
def settleLateLeakPull (G : SettleLateParameters) (profile : SettleLateProfile G late)
    (bit : Bool) : ℝ :=
  (1 - lateLeakInclusionProb G.toLateLeakParameters) * (1 - settleLateLeakProb G) *
    (if bit then (1 - settleLateQuietBitOne profile) * G.reward
      else -(settleLateQuietBitOne profile * G.reward))

/-- **The first-turn preference.** Under core play, and with the bit guessed
after every failure in which the listener knew it, opening at the first late
turn beats holding by `λ` times the late-turn game's label preference: the
answers after inclusions pull along one direction, and the leak pulls labels
`A` and `B` apart. -/
theorem settleLate_first_turn_preference (profile : SettleLateProfile G late)
    (secret : LateLeakType) (core : SettleLateCorePlay profile secret)
    (seen : ∀ ping, settleLateBitOneProb profile
      (.asked (settleLateSeenReport secret.1 ping none)) = if secret.1 then 1 else 0)
    (exposed : ∀ ping, settleLateBitOneProb profile
      (.asked (settleLateQuietReport ping none [0] (some secret.1))) = if secret.1 then 1 else 0) :
    settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none .opening -
        settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none .silent =
      settleLateLeakProb G * lateLeakLabelPreference
        (lateLeakInclusionProb G.toLateLeakParameters *
          (settleLateQuietSafe profile secret.1 - settleLateSeenSafe profile secret.1) *
            (G.reward / 2))
        (settleLateLeakPull G profile secret.1) secret.2 := by
  rw [settleLateEmitValue_opening_core profile secret core,
    settleLateEmitValue_silent_core profile secret core]
  simp only [settleLateSettleValue_seenHold, settleLateSettleValue_unseenHold, seen, exposed,
    settleLateQuietSafe, settleLateSeenSafe, settleLateLeakPull, settleLateQuietBitOne,
    settleLateSuccessValue, settleLateFailureValue]
  obtain ⟨bit, label⟩ := secret
  cases bit <;> cases label <;>
    simp only [lateLeakLabelPreference, lateLeakGuessGain, lateLeakBitOneGain,
      lateLeakBitZeroGain, reduceCtorEq, ite_true, ite_false, Bool.false_eq_true] <;> ring

end Vegas
