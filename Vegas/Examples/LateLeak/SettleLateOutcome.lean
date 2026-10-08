/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateIncentives

/-! # Outcome laws of the settle-late game

The outcome law is the law of the final state of play. In the intended outcome
every type opens at the protected turn, emits nothing more, and the listener
answers safely. Its mass at one type is the product of the probabilities of
these three choices, so an outcome law equal to the intended one forces all
three.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : SettleLateParameters} {late : Bool}

/-- The law of the final state of play from the initial state. -/
def settleLateOutcomeLaw (G : SettleLateParameters) (late : Bool)
    (profile : SettleLateProfile G late) : PMF SettleLateState :=
  ((settleLateModel G late).runBehavioralTerminalFrom (settleLate_terminates G late) profile
    (settleLateExecution G late).initHistory).map ExecutionProtocol.History.state

/-- The intended outcome: every type opens at the protected turn, emits no raw
signal, and the listener gives the safe answer. -/
def settleLateIntendedOutcome : PMF SettleLateState :=
  lateLeakPrior.map fun secret => .protectedDone secret none .safe

theorem settleLateOutcomeLaw_eq (G : SettleLateParameters) (late : Bool)
    (profile : SettleLateProfile G late) :
    settleLateOutcomeLaw G late profile = (settleLateFlow profile)^[6] (PMF.pure .initial) :=
  settleLate_terminal_map_state _ profile _

theorem settleLateIntendedOutcome_apply (secret : LateLeakType) :
    settleLateIntendedOutcome (.protectedDone secret none .safe) = lateLeakPrior secret :=
  pmf_map_apply_of_injective lateLeakPrior
    (f := fun secret => SettleLateState.protectedDone secret none .safe)
    (fun _ _ same => (SettleLateState.protectedDone.inj same).1) secret

/-- A payoff that vanishes at every final state after a deferral has value zero
at the first late turn. -/
theorem settleLateFirstValue_of_late_zero (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (zero : ∀ record answer, payoff (.finished record answer) = 0)
    (secret : LateLeakType) (early : Option Bool) :
    settleLateFirstValue profile payoff secret early = 0 := by
  simp only [settleLateFirstValue, settleLateEmitValue, settleLateWatchValue,
    settleLateSecondValue, settleLateSettleValue, settleLateAnswerValue, zero, expect_zero]

/-- The outcome law's mass on a type opening at the protected turn, emitting
nothing more, and the listener answering safely. -/
theorem settleLateOutcomeLaw_protected_safe (profile : SettleLateProfile G late)
    (secret : LateLeakType) :
    (settleLateOutcomeLaw G late profile (.protectedDone secret none .safe)).toReal =
      (lateLeakPrior secret).toReal *
        ((settleLateSenderLaw profile (.protectedTurn secret) (some (.emit .opening))).toReal *
          ((settleLateSenderLaw profile (.afterProtected secret) (some (.emit .silent))).toReal *
            settleLateSafeProb profile (.protectedAsked secret.1 none))) := by
  classical
  let target : SettleLateState := .protectedDone secret none .safe
  let indicator : SettleLateState → ℝ := fun state => if target = state then 1 else 0
  have read : (settleLateOutcomeLaw G late profile target).toReal =
      settleLateValue profile indicator (0 + 6) .initial := by
    rw [settleLateValue, ← settleLateOutcomeLaw_eq, expect_ite_eq, mul_one]
  have late_zero (other : LateLeakType) (early : Option Bool) :
      settleLateFirstValue profile indicator other early = 0 :=
    settleLateFirstValue_of_late_zero profile indicator (fun record answer => by
      simp [indicator, target]) other early
  have answer (other : LateLeakType) (talk : Option Bool) :
      settleLateProtectedAnswerValue profile indicator other talk =
        if other = secret ∧ talk = none then
          settleLateSafeProb profile (.protectedAsked secret.1 none)
        else 0 := by
    by_cases hit : other = secret ∧ talk = none
    · obtain ⟨rfl, rfl⟩ := hit
      simp only [and_self, ite_true]
      rw [settleLateProtectedAnswerValue, lateLeak_expect_two_point _ (some (.reply .safe)) _ 0]
      · simp [indicator, target, settleLateReplyOf, settleLateSafeProb]
      · intro choice supported different
        obtain ⟨reply, rfl, -⟩ := settleLateListenerLaw_support profile _ choice supported
        have : reply ≠ .safe := fun same => different (by rw [same])
        simp [indicator, target, settleLateReplyOf, Ne.symm this]
    · simp only [hit, ite_false]
      rw [settleLateProtectedAnswerValue, ← expect_zero (settleLateListenerLaw profile _)]
      apply expect_congr_on_support
      intro choice _
      simp only [indicator, target, SettleLateState.protectedDone.injEq]
      split
      · rename_i same
        exact (hit ⟨same.1.symm, same.2.1.symm⟩).elim
      · rfl
  have after (other : LateLeakType) :
      settleLateAfterValue profile indicator other =
        if secret = other then
          (settleLateSenderLaw profile (.afterProtected secret) (some (.emit .silent))).toReal *
            settleLateSafeProb profile (.protectedAsked secret.1 none)
        else 0 := by
    rw [settleLateAfterValue, lateLeak_expect_two_point _ (some (.emit .silent)) _ 0]
    · by_cases same : secret = other
      · subst same
        simp [settleLatePacketOf, SettleLatePacket.word, answer]
      · simp [settleLatePacketOf, SettleLatePacket.word, answer, same, Ne.symm same]
    · intro choice supported different
      obtain ⟨word, rfl, -⟩ := settleLateSenderLaw_support profile _ choice supported
      cases word with
      | none => exact (different rfl).elim
      | some word => simp [settleLatePacketOf, settleLateTalkPacket, SettleLatePacket.word, answer]
  have protectedValue (other : LateLeakType) :
      settleLateProtectedValue profile indicator other =
        if secret = other then
          (settleLateSenderLaw profile (.protectedTurn secret) (some (.emit .opening))).toReal *
            ((settleLateSenderLaw profile (.afterProtected secret) (some (.emit .silent))).toReal *
              settleLateSafeProb profile (.protectedAsked secret.1 none))
        else 0 := by
    rw [settleLateProtectedValue, lateLeak_expect_two_point _ (some (.emit .opening)) _ 0]
    · by_cases same : secret = other
      · subst same
        simp [settleLatePacketOf, settleLateProtectedEmitValue, after]
      · simp [settleLatePacketOf, settleLateProtectedEmitValue, after, same]
    · intro choice supported different
      obtain ⟨packet, rfl, -⟩ := settleLateSenderLaw_support profile _ choice supported
      have closed : packet ≠ .opening := fun same => different (by rw [same])
      simp [settleLatePacketOf, settleLateProtectedEmitValue, closed, late_zero]
  rw [read, settleLateValue_initial]
  simp only [protectedValue]
  rw [expect_ite_eq]

/-- An outcome law equal to the intended one forces opening at the protected
turn, no raw signal afterwards, and the safe answer. -/
theorem settleLate_intended_law_forces (profile : SettleLateProfile G late)
    (same : settleLateOutcomeLaw G late profile = settleLateIntendedOutcome)
    (secret : LateLeakType) :
    settleLateSenderLaw profile (.protectedTurn secret) = PMF.pure (some (.emit .opening)) ∧
      settleLateSenderLaw profile (.afterProtected secret) = PMF.pure (some (.emit .silent)) ∧
      settleLateListenerLaw profile (.protectedAsked secret.1 none) =
        PMF.pure (some (.reply .safe)) := by
  have mass := settleLateOutcomeLaw_protected_safe profile secret
  rw [same, settleLateIntendedOutcome_apply] at mass
  have positive : 0 < (lateLeakPrior secret).toReal :=
    ENNReal.toReal_pos (lateLeakPrior_ne_zero secret) (PMF.apply_ne_top _ _)
  set a := (settleLateSenderLaw profile (.protectedTurn secret) (some (.emit .opening))).toReal
  set b := (settleLateSenderLaw profile (.afterProtected secret) (some (.emit .silent))).toReal
  set c := settleLateSafeProb profile (.protectedAsked secret.1 none)
  have product : a * (b * c) = 1 := by
    have := mass.symm
    rw [mul_eq_left₀ positive.ne'] at this
    exact this
  have a0 : 0 ≤ a := ENNReal.toReal_nonneg
  have a1 : a ≤ 1 := lateLeak_toReal_le_one _ _
  have b0 : 0 ≤ b := ENNReal.toReal_nonneg
  have b1 : b ≤ 1 := lateLeak_toReal_le_one _ _
  have c0 : 0 ≤ c := settleLateSafeProb_nonneg _ _
  have c1 : c ≤ 1 := settleLateSafeProb_le_one _ _
  have bc1 : b * c ≤ 1 := by nlinarith
  have ha : a = 1 := by nlinarith [mul_nonneg b0 c0]
  have hbc : b * c = 1 := by rw [ha, one_mul] at product; exact product
  have hb : b = 1 := by nlinarith
  have hc : c = 1 := by rw [hb, one_mul] at hbc; exact hbc
  refine ⟨settleLate_law_eq_pure ((ENNReal.toReal_eq_one_iff _).mp ha),
    settleLate_law_eq_pure ((ENNReal.toReal_eq_one_iff _).mp hb),
    settleLate_law_eq_pure ((ENNReal.toReal_eq_one_iff _).mp hc)⟩

end Vegas
