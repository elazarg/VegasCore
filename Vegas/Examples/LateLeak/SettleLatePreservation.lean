/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateConsistency
import Vegas.Examples.LateLeak.SettleLateIntended

/-! # The settle-late runtime breaks sequential-equilibrium preservation

Suppose a sequential equilibrium of the settle-late game has the intended
outcome: every type opens at the protected turn, emits nothing more, and the
listener answers safely.

* After a silent deferral the sender plays the core packet at the second late
  turn, since raw signals and second openings are charged surely and never
  opening forfeits surely.
* Whatever the listener answers after a failure it never saw, the leak before
  the second late turn separates labels `A` and `B` in some class of the
  committed bit, so two types of that class strictly prefer opposite late
  turns, and each plays its preferred turn.
* Kreps-Wilson consistency then leaves one of the two types out of every
  inclusion set of that class seen by the leak, or out of every inclusion set
  not seen by it.
* There the listener guesses, and type `(v, A)` gets at least
  `q (λ R + (1 - λ) R/2) - (1 - q) (D + c)` by deferring silently to the
  corresponding late turn. When this exceeds `R/2`, its value at the protected
  turn, deferring contradicts rationality there.

For every reward scale `R > 0`, forfeit `D > R`, charge `c > R/2`, leak
probability `λ` in `(0, 1)` and listener packet cost, these margins hold for
every inclusion probability `q` above an explicit threshold below one.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : SettleLateParameters}

/-! ## Deferring to a guessing listener -/

/-- If the listener guesses after every first-turn inclusion it saw, type
`(v, A)` gets at least `q (λ R + (1 - λ) R/2) - (1 - q) (D + c)` by opening at
the first late turn. -/
theorem settleLateEmitValue_opening_guessed {late : Bool} (profile : SettleLateProfile G late)
    (R0 : 0 ≤ G.reward) (c0 : 0 ≤ G.dropCharge) (bit : Bool)
    (core : SettleLateCorePlay profile (bit, .a))
    (guessing : ∀ ping,
      settleLateSafeProb profile (.asked (settleLateSeenReport bit ping (some 0))) = 0) :
    lateLeakInclusionProb G.toLateLeakParameters *
        (settleLateLeakProb G * G.reward + (1 - settleLateLeakProb G) * (G.reward / 2)) -
      (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
      settleLateEmitValue profile (settleLateStatePayoff G .sender) (bit, .a) none .opening := by
  have hold := (settleLateEmitValue_core_ge profile R0 c0 (bit, .a) core).1
  simp only [settleLateFloor, reduceCtorEq, ite_false] at hold
  rw [settleLateEmitValue_opening_core profile (bit, .a) core,
    settleLateSettleValue_seenHold, settleLateSettleValue_seenHold, guessing, guessing]
  have q0 := (lateLeakInclusionProb_pos G.toLateLeakParameters).le
  have q1 := sub_nonneg.mpr (lateLeakInclusionProb_lt_one G.toLateLeakParameters).le
  have l0 := (settleLateLeakProb_pos G).le
  have l1 := sub_nonneg.mpr (settleLateLeakProb_lt_one G).le
  have win : settleLateSuccessValue G 0 (bit, LateLeakLabel.a).2 = G.reward := by
    simp [settleLateSuccessValue, lateLeakGuessGain]
  rw [win]
  have fail (ping : Bool) := settleLateFailureValue_nonneg (G := G) R0
    (settleLateBitOneProb_nonneg profile (.asked (settleLateSeenReport bit ping none)))
    (settleLateBitOneProb_le_one profile (.asked (settleLateSeenReport bit ping none)))
    (bit, LateLeakLabel.a).2
  have seen (ping : Bool) :
      lateLeakInclusionProb G.toLateLeakParameters * G.reward -
          (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
        lateLeakInclusionProb G.toLateLeakParameters * G.reward +
          (1 - lateLeakInclusionProb G.toLateLeakParameters) *
            (settleLateFailureValue G
              (settleLateBitOneProb profile (.asked (settleLateSeenReport bit ping none)))
              (bit, LateLeakLabel.a).2 - G.forfeit - G.dropCharge) := by
    nlinarith [mul_nonneg q1 (fail ping)]
  have p0 := settleLatePingProb_nonneg profile (.watching none (.opening (bit, LateLeakLabel.a).1))
  have p1 := settleLatePingProb_le_one profile (.watching none (.opening (bit, LateLeakLabel.a).1))
  have watch := add_le_add (mul_le_mul_of_nonneg_left (seen true) p0)
    (mul_le_mul_of_nonneg_left (seen false) (sub_nonneg.mpr p1))
  nlinarith [mul_le_mul_of_nonneg_left watch l0, mul_le_mul_of_nonneg_left hold l1]

/-- If the listener guesses after every inclusion it did not see before, type
`(v, A)` gets at least `q R - (1 - q) (D + c)` by holding at the first late
turn and opening at the second. -/
theorem settleLateEmitValue_silent_guessed {late : Bool} (profile : SettleLateProfile G late)
    (R0 : 0 ≤ G.reward) (bit : Bool) (core : SettleLateCorePlay profile (bit, .a))
    (guessing : ∀ ping,
      settleLateSafeProb profile (.asked (settleLateQuietReport ping (some 0) [] (some bit))) = 0) :
    lateLeakInclusionProb G.toLateLeakParameters * G.reward -
        (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
      settleLateEmitValue profile (settleLateStatePayoff G .sender) (bit, .a) none .silent := by
  rw [settleLateEmitValue_silent_core profile (bit, .a) core,
    settleLateSettleValue_unseenHold, settleLateSettleValue_unseenHold, guessing, guessing]
  have q1 := sub_nonneg.mpr (lateLeakInclusionProb_lt_one G.toLateLeakParameters).le
  have l0 := (settleLateLeakProb_pos G).le
  have l1 := sub_nonneg.mpr (settleLateLeakProb_lt_one G).le
  have win : settleLateSuccessValue G 0 (bit, LateLeakLabel.a).2 = G.reward := by
    simp [settleLateSuccessValue, lateLeakGuessGain]
  rw [win]
  have fail (view : SettleLateView) := settleLateFailureValue_nonneg (G := G) R0
    (settleLateBitOneProb_nonneg profile view) (settleLateBitOneProb_le_one profile view)
    (bit, LateLeakLabel.a).2
  have mixed (ping : Bool) :
      -(G.forfeit + G.dropCharge) ≤
        settleLateLeakProb G * (settleLateFailureValue G (settleLateBitOneProb profile
            (.asked (settleLateQuietReport ping none [0] (some (bit, LateLeakLabel.a).1))))
            (bit, LateLeakLabel.a).2 - G.forfeit - G.dropCharge) +
          (1 - settleLateLeakProb G) * (settleLateFailureValue G (settleLateBitOneProb profile
            (.asked (settleLateQuietReport ping none [] none))) (bit, LateLeakLabel.a).2 -
              G.forfeit - G.dropCharge) := by
    nlinarith [mul_nonneg l0 (fail (.asked (settleLateQuietReport ping none [0]
      (some (bit, LateLeakLabel.a).1)))),
      mul_nonneg l1 (fail (.asked (settleLateQuietReport ping none [] none)))]
  have quiet (ping : Bool) := mul_le_mul_of_nonneg_left (mixed ping) q1
  have p0 := settleLatePingProb_nonneg profile (.watching none .nothing)
  have p1 := settleLatePingProb_le_one profile (.watching none .nothing)
  nlinarith [mul_le_mul_of_nonneg_left (quiet true) p0,
    mul_le_mul_of_nonneg_left (quiet false) (sub_nonneg.mpr p1)]

/-- Under the intended outcome, type `(v, A)` cannot gain by deferring silently
and emitting one first-turn packet. -/
theorem settleLate_deferral_bounded
    {A : (settleLateModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G true) (settleLatePayoff G true))
    (same : settleLateOutcomeLaw G true A.strategy = settleLateIntendedOutcome)
    (secret : LateLeakType) (packet : SettleLatePacket) :
    settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) secret none packet ≤
      G.reward / 2 := by
  obtain ⟨opens, quiet, safe⟩ := settleLate_intended_law_forces A.strategy same secret
  have optimal := settleLate_rational_at_state rational (settleLateProtectedSite G true secret)
    (fun history => settleLate_protectedTurn_fiber history)
    (settleLateDeferral G (A.strategy .sender) secret packet)
  rw [settleLate_deferral_value, settleLate_protected_value_of_safe A.strategy secret opens quiet
    safe] at optimal
  exact optimal

/-! ## No preserving equilibrium -/

/-- **No sequential equilibrium of the settle-late game has the intended
outcome law**, when deferring pays. -/
theorem settleLate_no_intended_equilibrium (pays : G.DeferralPays)
    (A : (settleLateModel G true).BehavioralAssessment)
    (equilibrium : A.IsSequentialEquilibrium (settleLate_antichain G true)
      (settleLate_terminates G true) (settleLatePayoff G true)) :
    settleLateOutcomeLaw G true A.strategy ≠ settleLateIntendedOutcome := by
  intro same
  obtain ⟨rational, consistent⟩ := equilibrium
  have R0 := pays.reward_pos.le
  have c0 : 0 ≤ G.dropCharge := by linarith [pays.charge_gt, pays.reward_pos]
  obtain ⟨bit, sender, holder, senderPrefers, holderPrefers⟩ :=
    settleLate_opposite_preferences pays rational
  have sends := settleLate_rational_first_turn pays rational (bit, sender) .opening .silent
    (Or.inl ⟨rfl, rfl⟩) senderPrefers
  have holds := settleLate_rational_first_turn pays rational (bit, holder) .silent .opening
    (Or.inr ⟨rfl, rfl⟩) holderPrefers
  have core (label : LateLeakLabel) := settleLate_rational_corePlay pays rational (bit, label)
  have half := pays.guess_beats_safe
  rcases settleLate_consistent_face consistent bit sender holder sends holds (core sender)
      (core holder) with seenFace | quietFace
  · have guessing (ping : Bool) :
        settleLateSafeProb A.strategy (.asked (settleLateSeenReport bit ping (some 0))) = 0 :=
      settleLate_rational_guesses rational (settleLateSeenSuccessSite G bit ping) _ rfl rfl holder
        (seenFace ping)
    have gain := settleLateEmitValue_opening_guessed A.strategy R0 c0 bit (core .a) guessing
    have bound := settleLate_deferral_bounded rational same (bit, .a) .opening
    linarith
  · have guessing (ping : Bool) :
        settleLateSafeProb A.strategy
          (.asked (settleLateQuietReport ping (some 0) [] (some bit))) = 0 :=
      settleLate_rational_guesses rational (settleLateQuietSuccessSite G bit ping) _ rfl rfl sender
        (quietFace ping)
    have gain := settleLateEmitValue_silent_guessed A.strategy R0 bit (core .a) guessing
    have bound := settleLate_deferral_bounded rational same (bit, .a) .silent
    have l1 := (settleLateLeakProb_lt_one G).le
    have q0 := (lateLeakInclusionProb_pos G.toLateLeakParameters).le
    have mix : settleLateLeakProb G * G.reward + (1 - settleLateLeakProb G) * (G.reward / 2) ≤
        G.reward := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left mix q0]

/-- **No sequential equilibrium of the settle-late game preserves the intended
outcome when deferring pays.** The intended game has a sequential equilibrium;
each of its sequential equilibria has the intended outcome law; and no
sequential equilibrium of the settle-late game has that law. -/
theorem settleLate_intended_outcome_not_preserved (G : SettleLateParameters)
    (pays : G.DeferralPays) :
    (∃ A : (settleLateModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (settleLate_antichain G false) (settleLate_terminates G false)
        (settleLatePayoff G false)) ∧
    (∀ A : (settleLateModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (settleLate_antichain G false) (settleLate_terminates G false)
          (settleLatePayoff G false) →
        settleLateOutcomeLaw G false A.strategy = settleLateIntendedOutcome) ∧
    ∀ A : (settleLateModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (settleLate_antichain G true) (settleLate_terminates G true)
          (settleLatePayoff G true) →
        settleLateOutcomeLaw G true A.strategy ≠ settleLateIntendedOutcome :=
  ⟨(settleLate_intended_equilibria G).1, (settleLate_intended_equilibria G).2,
    settleLate_no_intended_equilibrium pays⟩

/-! ## Every margin -/

/-- An inclusion probability above which deferring pays in the settle-late
game, for reward scale `R`, forfeit `D`, charge `c` and leak probability `λ`:
the larger of `(D + c + R - min c D) / (D + c + R/2)`, above which packets
other than the core packet never pay, and
`(D + c + R/2) / (D + c + R/2 + λ R/2)`, above which a guess after a seen
first-turn inclusion beats the safe answer at the protected turn. -/
def settleLateInclusionThreshold (R D c leak : ℝ) : ℝ :=
  max ((D + c + R - min c D) / (D + c + R / 2))
    ((D + c + R / 2) / (D + c + R / 2 + leak * (R / 2)))

/-- For `R > 0`, `D > R`, `c > R/2` and `λ > 0` the threshold is below one. -/
theorem settleLateInclusionThreshold_lt_one {R D c leak : ℝ} (reward_pos : 0 < R)
    (margin : R < D) (charge : R / 2 < c) (leak_pos : 0 < leak) :
    settleLateInclusionThreshold R D c leak < 1 := by
  have minimum : R / 2 < min c D := lt_min charge (by linarith)
  have spread : 0 < leak * (R / 2) := mul_pos leak_pos (by linarith)
  exact max_lt ((div_lt_one (by linarith)).mpr (by linarith))
    ((div_lt_one (by linarith)).mpr (by linarith))

/-- Above the threshold deferring pays. -/
theorem settleLate_deferralPays_of_threshold {R D c : ℝ} (reward_pos : 0 < R) (margin : R < D)
    (charge : R / 2 < c) (leak : Set.Ioo (0 : ℝ) 1) (packetCost : ℝ) (q : Set.Ioo (0 : ℝ) 1)
    (above : settleLateInclusionThreshold R D c leak < q) :
    (⟨⟨R, D, c, q⟩, leak, packetCost⟩ : SettleLateParameters).DeferralPays := by
  obtain ⟨extra, guess⟩ := max_lt_iff.mp above
  have minimum : min c D ≤ c := min_le_left c D
  have spread : 0 < (leak : ℝ) * (R / 2) := mul_pos leak.2.1 (by linarith)
  rw [div_lt_iff₀ (by linarith)] at extra
  rw [div_lt_iff₀ (by linarith)] at guess
  refine ⟨reward_pos, margin, charge, ?_, ?_⟩ <;>
    simp only [lateLeakInclusionProb, settleLateLeakProb] <;> nlinarith

/-- **No margin on the forfeit and the charge restores preservation in the
settle-late runtime.** For every reward scale `R > 0`, forfeit `D > R`, charge
`c > R/2`, leak probability `λ` in `(0, 1)` and listener packet cost c_L, the
inclusion threshold is below one, and for every inclusion probability `q`
above it the intended game has a sequential equilibrium, all its sequential
equilibria have the intended outcome law, and no sequential equilibrium of the
settle-late game with these parameters has that law. -/
theorem settleLate_not_preserved_for_every_margin (R D c : ℝ) (reward_pos : 0 < R)
    (margin : R < D) (charge : R / 2 < c) (leak : Set.Ioo (0 : ℝ) 1) (packetCost : ℝ) :
    settleLateInclusionThreshold R D c leak < 1 ∧
    ∀ q : Set.Ioo (0 : ℝ) 1, settleLateInclusionThreshold R D c leak < q →
      (∃ A : (settleLateModel ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false).BehavioralAssessment,
        A.IsSequentialEquilibrium (settleLate_antichain ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)
          (settleLate_terminates ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)
          (settleLatePayoff ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)) ∧
      (∀ A : (settleLateModel ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false).BehavioralAssessment,
        A.IsSequentialEquilibrium (settleLate_antichain ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)
            (settleLate_terminates ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)
            (settleLatePayoff ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false) →
          settleLateOutcomeLaw ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false A.strategy =
            settleLateIntendedOutcome) ∧
      ∀ A : (settleLateModel ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true).BehavioralAssessment,
        A.IsSequentialEquilibrium (settleLate_antichain ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true)
            (settleLate_terminates ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true)
            (settleLatePayoff ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true) →
          settleLateOutcomeLaw ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true A.strategy ≠
            settleLateIntendedOutcome :=
  ⟨settleLateInclusionThreshold_lt_one reward_pos margin charge leak.2.1, fun q above =>
    settleLate_intended_outcome_not_preserved _
      (settleLate_deferralPays_of_threshold reward_pos margin charge leak packetCost q above)⟩

end Vegas
