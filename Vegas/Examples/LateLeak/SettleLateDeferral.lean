/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateValues

/-! # Deferring the protected opening in the settle-late game

In every sequentially rational assessment of the settle-late game, two types
of one class of the committed bit strictly prefer opposite late turns after a
silent protected turn, and each plays its preferred turn with probability one.
A type that deviates from opening at the protected turn to a silent deferral
followed by one late opening gets the value of that opening under the
listener's play.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : SettleLateParameters} {late : Bool}

/-! ## Answers after a failure with a known bit -/

theorem settleLate_mem_support_of_pos {α : Type*} [DecidableEq α] (law : PMF α) (a : α)
    (positive : 0 < expect law fun x => if a = x then 1 else 0) : a ∈ law.support := by
  rw [expect_ite_eq, mul_one] at positive
  exact (PMF.mem_support_iff _ _).mpr fun zero => by simp [zero] at positive

theorem settleLateFateLaw_seenFailure_support :
    (⟨none, false, false⟩ : SettleLateFate) ∈
      (settleLateFateLaw G (.opening true) .silent).support := by
  apply settleLate_mem_support_of_pos
  rw [settleLate_expect_fate_seenHold]
  simp only [SettleLateFate.mk.injEq, reduceCtorEq, false_and, ite_false, and_self, ite_true,
    mul_zero, mul_one, zero_add]
  exact sub_pos.mpr (lateLeakInclusionProb_lt_one G.toLateLeakParameters)

theorem settleLateFateLaw_exposedFailure_support :
    (⟨none, true, false⟩ : SettleLateFate) ∈
      (settleLateFateLaw G (.opening false) .silent).support := by
  apply settleLate_mem_support_of_pos
  rw [settleLate_expect_fate_unseenHold]
  simp only [SettleLateFate.mk.injEq, reduceCtorEq, false_and, ite_false, and_self, ite_true,
    mul_zero, mul_one, zero_add, Bool.true_eq_false, and_false, add_zero]
  exact mul_pos (sub_pos.mpr (lateLeakInclusionProb_lt_one G.toLateLeakParameters))
    (settleLateLeakProb_pos G)

/-- The listener's information set at an answer reached by a history. -/
def settleLateAnswerSite (G : SettleLateParameters) (record : SettleLateRecord)
    (supported : record.fate ∈ (settleLateFateLaw G record.first record.second).support)
    (answer : LateLeakAnswer) (fits : answer.fitsOutcome record.report.included.isSome = true) :
    (settleLateModel G true).InformationSite .listener :=
  settleLateSite G true .listener (settleLateAnswerHistory G record supported) (.reply answer)
    ⟨answer, rfl, fits⟩
    (by simp [settleLateAnswerHistory, settleLateExtend, SettleLateState.IsFinished])

/-- After a first-turn opening it saw is dropped, the listener guesses the
bit. -/
theorem settleLate_rational_seen_failure {A : (settleLateModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G true) (settleLatePayoff G true))
    (bit ping : Bool) :
    settleLateBitOneProb A.strategy (.asked (settleLateSeenReport bit ping none)) =
      if bit then 1 else 0 :=
  settleLate_rational_known_failure rational
    (settleLateAnswerSite G ⟨(bit, .a), none, .opening true, ping, .silent, ⟨none, false, false⟩⟩
      settleLateFateLaw_seenFailure_support (.failure true) rfl)
    _ rfl rfl bit rfl

/-- After a dropped opening it sees when it answers, the listener guesses the
bit. -/
theorem settleLate_rational_exposed_failure {A : (settleLateModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G true) (settleLatePayoff G true))
    (bit ping : Bool) :
    settleLateBitOneProb A.strategy (.asked (settleLateQuietReport ping none [0] (some bit))) =
      if bit then 1 else 0 :=
  settleLate_rational_known_failure rational
    (settleLateAnswerSite G ⟨(bit, .a), none, .opening false, ping, .silent, ⟨none, true, false⟩⟩
      settleLateFateLaw_exposedFailure_support (.failure true) rfl)
    _ rfl rfl bit rfl

/-! ## Opposite preferences -/

/-- **Opposite strict preferences.** In every sequentially rational
assessment, two types of one class strictly prefer opposite late turns after
a silent protected turn. -/
theorem settleLate_opposite_preferences (pays : G.DeferralPays)
    {A : (settleLateModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G true) (settleLatePayoff G true)) :
    ∃ bit sender holder,
      settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) (bit, sender) none .silent <
        settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) (bit, sender) none
          .opening ∧
      settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) (bit, holder) none
          .opening <
        settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) (bit, holder) none
          .silent := by
  have dropped : (1 - lateLeakInclusionProb G.toLateLeakParameters) ≠ 0 :=
    (sub_pos.mpr (lateLeakInclusionProb_lt_one G.toLateLeakParameters)).ne'
  have unseen : (1 - settleLateLeakProb G) ≠ 0 := (sub_pos.mpr (settleLateLeakProb_lt_one G)).ne'
  obtain ⟨bit, separates⟩ : ∃ bit, settleLateLeakPull G A.strategy bit ≠ 0 := by
    by_cases sure : settleLateQuietBitOne A.strategy = 1
    · refine ⟨false, ?_⟩
      simp only [settleLateLeakPull, Bool.false_eq_true, ite_false, sure, one_mul]
      exact mul_ne_zero (mul_ne_zero dropped unseen) (neg_ne_zero.mpr pays.reward_pos.ne')
    · refine ⟨true, ?_⟩
      simp only [settleLateLeakPull, ite_true]
      exact mul_ne_zero (mul_ne_zero dropped unseen)
        (mul_ne_zero (sub_ne_zero.mpr (Ne.symm sure)) pays.reward_pos.ne')
  obtain ⟨sender, holder, prefers, avoids⟩ :=
    lateLeak_opposite_label_preferences _ _ separates
  have identity (label : LateLeakLabel) :=
    settleLate_first_turn_preference A.strategy (bit, label)
      (settleLate_rational_corePlay pays rational (bit, label))
      (settleLate_rational_seen_failure rational bit)
      (settleLate_rational_exposed_failure rational bit)
  have leak := settleLateLeakProb_pos G
  refine ⟨bit, sender, holder, ?_, ?_⟩
  · have := identity sender
    have := mul_pos leak prefers
    linarith
  · have := identity holder
    have := mul_neg_of_pos_of_neg leak avoids
    linarith

/-! ## Rational play at the first late turn -/

theorem settleLateEmitValue_update_agree (profile : SettleLateProfile G late)
    (policy : (settleLateModel G late).BehavioralPolicy .sender)
    (agree : ∀ secret early packet ping,
      policy (.secondTurn secret early packet ping) =
        profile .sender (.secondTurn secret early packet ping))
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (early : Option Bool)
    (packet : SettleLatePacket) :
    settleLateEmitValue (settleLateUpdate profile .sender policy) payoff secret early packet =
      settleLateEmitValue profile payoff secret early packet := by
  simp only [settleLateEmitValue, settleLateWatchValue, settleLateSecondValue,
    settleLateListenerLaw_update_sender, settleLateSenderLaw_update_sender, agree,
    settleLateSettleValue_update_sender]
  rfl

/-- After a first-turn raw signal the sender is charged on every path. -/
theorem settleLateEmitValue_signal_le (profile : SettleLateProfile G late) (R0 : 0 ≤ G.reward)
    (D0 : 0 ≤ G.forfeit) (secret : LateLeakType) (word : Bool) :
    settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none (.signal word) ≤
      settleLateTop G secret.2 - G.dropCharge := by
  have settle (ping : Bool) (second : SettleLatePacket) :
      settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none (.signal word)
          ping second ≤ settleLateTop G secret.2 - G.dropCharge := by
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
    intro fate _
    have bound := settleLateAnswerValue_le profile R0
      ⟨secret, none, .signal word, ping, second, fate⟩
    have charged : (⟨secret, none, .signal word, ping, second, fate⟩ :
        SettleLateRecord).charged = true := by
      simp [SettleLateRecord.charged, SettleLateFirst.signaled]
    rw [charged] at bound
    simp only [ite_true] at bound
    split at bound <;> linarith
  have second (ping : Bool) :
      settleLateSecondValue profile (settleLateStatePayoff G .sender) secret none (.signal word)
          ping ≤ settleLateTop G secret.2 - G.dropCharge :=
    expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun choice _ => settle ping _
  rw [settleLateEmitValue_signal, settleLateWatchValue_eq]
  have p0 := settleLatePingProb_nonneg profile
    (.watching none ((SettleLateFirst.signal word).glimpse secret.1))
  have p1 := settleLatePingProb_le_one profile
    (.watching none ((SettleLateFirst.signal word).glimpse secret.1))
  nlinarith [mul_le_mul_of_nonneg_left (second true) p0,
    mul_le_mul_of_nonneg_left (second false) (sub_nonneg.mpr p1)]

/-- Under core play both late plans lose at most `(1 - q) (D + c)` below the
label's smallest payoff after an inclusion. -/
theorem settleLateEmitValue_core_ge (profile : SettleLateProfile G late) (R0 : 0 ≤ G.reward)
    (c0 : 0 ≤ G.dropCharge) (secret : LateLeakType) (core : SettleLateCorePlay profile secret) :
    (lateLeakInclusionProb G.toLateLeakParameters * settleLateFloor G secret.2 -
        (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
      settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none .silent) ∧
    (lateLeakInclusionProb G.toLateLeakParameters * settleLateFloor G secret.2 -
        (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
      settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none .opening) := by
  have bound (first : SettleLateFirst) (plain : first.Plain) (ping : Bool) :=
    settleLateSettleValue_core_ge profile R0 c0 secret plain ping
  have unseen (ping : Bool) := bound (.opening false) (Or.inr ⟨false, rfl⟩) ping
  have seen (ping : Bool) := bound (.opening true) (Or.inr ⟨true, rfl⟩) ping
  simp only [SettleLateFirst.packet, settleLateCorePacket] at unseen seen
  have hold : lateLeakInclusionProb G.toLateLeakParameters * settleLateFloor G secret.2 -
        (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
      settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none .silent := by
    rw [settleLateEmitValue_silent_core profile secret core]
    have p0 := settleLatePingProb_nonneg profile (.watching none .nothing)
    have p1 := settleLatePingProb_le_one profile (.watching none .nothing)
    nlinarith [mul_le_mul_of_nonneg_left (unseen true) p0,
      mul_le_mul_of_nonneg_left (unseen false) (sub_nonneg.mpr p1)]
  refine ⟨hold, ?_⟩
  rw [settleLateEmitValue_opening_core profile secret core]
  have p0 := settleLatePingProb_nonneg profile (.watching none (.opening secret.1))
  have p1 := settleLatePingProb_le_one profile (.watching none (.opening secret.1))
  have l0 := (settleLateLeakProb_pos G).le
  have l1 := sub_nonneg.mpr (settleLateLeakProb_lt_one G).le
  have watch : lateLeakInclusionProb G.toLateLeakParameters * settleLateFloor G secret.2 -
        (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
      settleLatePingProb profile (.watching none (.opening secret.1)) *
          settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none
            (.opening true) true .silent +
        (1 - settleLatePingProb profile (.watching none (.opening secret.1))) *
          settleLateSettleValue profile (settleLateStatePayoff G .sender) secret none
            (.opening true) false .silent := by
    nlinarith [mul_le_mul_of_nonneg_left (seen true) p0,
      mul_le_mul_of_nonneg_left (seen false) (sub_nonneg.mpr p1)]
  nlinarith [mul_le_mul_of_nonneg_left watch l0, mul_le_mul_of_nonneg_left hold l1]

theorem settleLate_firstTurn_menu (secret : LateLeakType) (early : Option Bool)
    (packet : SettleLatePacket) :
    some (SettleLateMove.emit packet) ∈ settleLateMenu late (.firstTurn secret early) :=
  ⟨packet, rfl⟩

/-- **The first late turn.** A sequentially rational sender who deferred
silently plays a strictly preferred late plan with probability one. -/
theorem settleLate_rational_first_turn (pays : G.DeferralPays)
    {A : (settleLateModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G true) (settleLatePayoff G true))
    (secret : LateLeakType) (preferred unpreferred : SettleLatePacket)
    (plans : (preferred = .opening ∧ unpreferred = .silent) ∨
      (preferred = .silent ∧ unpreferred = .opening))
    (strict : settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) secret none
        unpreferred <
      settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) secret none preferred) :
    settleLateSenderLaw A.strategy (.firstTurn secret none) =
      PMF.pure (some (.emit preferred)) := by
  have core := settleLate_rational_corePlay pays rational secret
  have R0 := pays.reward_pos.le
  have c0 : 0 ≤ G.dropCharge := by linarith [pays.charge_gt]
  have D0 : 0 ≤ G.forfeit := by linarith [pays.forfeit_gt]
  obtain ⟨holdBound, openBound⟩ := settleLateEmitValue_core_ge A.strategy R0 c0 secret core
  have gap := pays.core_gap secret.2
  have minC := min_le_left G.dropCharge G.forfeit
  let site := settleLateFirstSite G secret none
  have at_state (history : (settleLateModel G true).InformationHistory .sender site.1) :
      history.1.state = .firstLate secret none := settleLate_firstTurn_fiber history
  let value (choice : Option SettleLateMove) : ℝ :=
    settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) secret none
      (settleLatePacketOf choice)
  have current : settleLateValue A.strategy (settleLateStatePayoff G .sender) 6
      (.firstLate secret none) = expect (settleLateSenderLaw A.strategy (.firstTurn secret none))
        value :=
    settleLateValue_firstLate _ _ 2 secret none
  let deviation := (A.strategy .sender).commit site.1
    ⟨some (.emit preferred), settleLate_firstTurn_menu (late := true) secret none preferred⟩
  have deviated : settleLateValue (settleLateUpdate A.strategy .sender deviation)
      (settleLateStatePayoff G .sender) 6 (.firstLate secret none) =
        value (some (.emit preferred)) := by
    rw [show (6 : ℕ) = 2 + 4 from rfl, settleLateValue_firstLate, settleLateFirstValue,
      settleLateSenderLaw_update_sender]
    change expect (((A.strategy .sender).commit site.1
      ⟨some (.emit preferred), settleLate_firstTurn_menu (late := true) secret none preferred⟩
        site.1).map Subtype.val) _ = _
    rw [InformationModel.BehavioralPolicy.commit_self (M := settleLateModel G true), PMF.pure_map,
      expect_pure]
    exact settleLateEmitValue_update_agree A.strategy deviation (fun _ _ _ _ =>
      InformationModel.BehavioralPolicy.commit_of_ne (M := settleLateModel G true) _ _ _
        (by simp [site, settleLateFirstSite, settleLateSite, settleLateDeferredHistory,
          settleLateExtend, settleLateView])) _ _ _ _
  have optimal := settleLate_rational_at_state rational site at_state deviation
  rw [deviated, current] at optimal
  apply settleLate_law_eq_pure
  have signal (word : Bool) := settleLateEmitValue_signal_le A.strategy R0 D0 secret word
  have preferredBound : lateLeakInclusionProb G.toLateLeakParameters *
        settleLateFloor G secret.2 -
      (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) ≤
      value (some (.emit preferred)) := by
    rcases plans with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact openBound
    · exact holdBound
  refine pmf_apply_eq_one_of_dominant_at _ value _
    (lt_min (sub_pos.mpr strict) (sub_pos.mpr (lt_of_lt_of_le (by linarith) preferredBound)) :
      0 < min (value (some (.emit preferred)) - value (some (.emit unpreferred)))
        (value (some (.emit preferred)) - (settleLateTop G secret.2 - G.dropCharge)))
    ?_ optimal
  intro choice supported different
  obtain ⟨packet, rfl⟩ := settleLateSenderLaw_support A.strategy _ choice supported
  have notPreferred : packet ≠ preferred := fun same => different (by rw [same])
  have m1 := min_le_left (value (some (.emit preferred)) - value (some (.emit unpreferred)))
    (value (some (.emit preferred)) - (settleLateTop G secret.2 - G.dropCharge))
  have m2 := min_le_right (value (some (.emit preferred)) - value (some (.emit unpreferred)))
    (value (some (.emit preferred)) - (settleLateTop G secret.2 - G.dropCharge))
  cases packet with
  | signal word =>
      have := signal word
      change settleLateEmitValue A.strategy (settleLateStatePayoff G .sender) secret none
        (.signal word) + _ ≤ _
      linarith
  | silent =>
      rcases plans with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · linarith
      · exact (notPreferred rfl).elim
  | opening =>
      rcases plans with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (notPreferred rfl).elim
      · linarith

/-! ## The protected turn -/

theorem settleLate_protectedTurn_menu (secret : LateLeakType) (packet : SettleLatePacket) :
    some (SettleLateMove.emit packet) ∈ settleLateMenu true (.protectedTurn secret) :=
  ⟨packet, rfl, Or.inl rfl⟩

/-- The sender's deviation to a silent deferral followed by one first-turn
packet, keeping the rest of a policy. -/
def settleLateDeferral (G : SettleLateParameters)
    (policy : (settleLateModel G true).BehavioralPolicy .sender) (secret : LateLeakType)
    (packet : SettleLatePacket) : (settleLateModel G true).BehavioralPolicy .sender :=
  (policy.commit (.protectedTurn secret)
    ⟨some (.emit .silent), settleLate_protectedTurn_menu secret .silent⟩).commit
      (.firstTurn secret none)
      ⟨some (.emit packet), settleLate_firstTurn_menu (late := true) secret none packet⟩

/-- Deferring silently and emitting one first-turn packet is worth that
packet's value under the rest of the profile. -/
theorem settleLate_deferral_value (profile : SettleLateProfile G true) (secret : LateLeakType)
    (packet : SettleLatePacket) :
    settleLateValue (settleLateUpdate profile .sender
        (settleLateDeferral G (profile .sender) secret packet))
        (settleLateStatePayoff G .sender) 6 (.protectedTurn secret) =
      settleLateEmitValue profile (settleLateStatePayoff G .sender) secret none packet := by
  rw [show (6 : ℕ) = 1 + 5 from rfl, settleLateValue_protectedTurn, settleLateProtectedValue,
    settleLateSenderLaw_update_sender, settleLateDeferral,
    InformationModel.BehavioralPolicy.commit_of_ne (M := settleLateModel G true) _ _ _
      (by simp), InformationModel.BehavioralPolicy.commit_self (M := settleLateModel G true),
    PMF.pure_map, expect_pure]
  simp only [settleLatePacketOf, settleLateProtectedEmitValue, reduceCtorEq, ite_false,
    SettleLatePacket.word, settleLateFirstValue, settleLateSenderLaw_update_sender]
  rw [InformationModel.BehavioralPolicy.commit_self (M := settleLateModel G true), PMF.pure_map,
    expect_pure]
  exact settleLateEmitValue_update_agree profile _ (fun _ _ _ _ => by
    rw [InformationModel.BehavioralPolicy.commit_of_ne (M := settleLateModel G true) _ _ _
        (by simp),
      InformationModel.BehavioralPolicy.commit_of_ne (M := settleLateModel G true) _ _ _
        (by simp)]) _ _ _ _

/-- The value of the protected turn when the type opens there, adds no raw
signal and the listener answers safely. -/
theorem settleLate_protected_value_of_safe (profile : SettleLateProfile G late)
    (secret : LateLeakType)
    (opens : settleLateSenderLaw profile (.protectedTurn secret) = PMF.pure (some (.emit .opening)))
    (quiet : settleLateSenderLaw profile (.afterProtected secret) =
      PMF.pure (some (.emit .silent)))
    (safe : settleLateListenerLaw profile (.protectedAsked secret.1 none) =
      PMF.pure (some (.reply .safe))) :
    settleLateValue profile (settleLateStatePayoff G .sender) 6 (.protectedTurn secret) =
      G.reward / 2 := by
  rw [show (6 : ℕ) = 1 + 5 from rfl, settleLateValue_protectedTurn, settleLateProtectedValue,
    opens, expect_pure]
  simp only [settleLatePacketOf, settleLateProtectedEmitValue, ite_true, settleLateAfterValue,
    quiet, expect_pure, SettleLatePacket.word, settleLateProtectedAnswerValue, safe,
    settleLateReplyOf, settleLateStatePayoff, settleLateSenderBase, Option.isSome_none,
    Bool.false_eq_true, ite_false, sub_zero]

end Vegas
