/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateIncentives

/-! # Rational play at the late turns of the settle-late game

After a silent protected turn, a sequentially rational sender plays the core
packet at the second late turn: it holds after a first-turn opening and opens
otherwise. With that continuation, the values of opening and of holding at the
first late turn are the late-turn game's values with the leak scaled by `λ`:
their difference is `λ` times a label preference whose leak pull vanishes in at
most one class of the committed bit.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : SettleLateParameters} {late : Bool}

/-! ## Margins -/

/-- The margins under which deferring pays in the settle-late game. The reward
scale is positive, the forfeit exceeds it and the charge exceeds half of it;
packets other than the core packet never pay,
`(1 - q) (D + c + R/2) < min c D - R/2`; and a label guess after every
first-turn inclusion the listener saw beats the safe answer at the protected
turn, `q (λ R + (1 - λ) R/2) - (1 - q) (D + c) > R/2`. -/
structure SettleLateParameters.DeferralPays (G : SettleLateParameters) : Prop where
  reward_pos : 0 < G.reward
  forfeit_gt : G.reward < G.forfeit
  charge_gt : G.reward / 2 < G.dropCharge
  extra_packets :
    (1 - lateLeakInclusionProb G.toLateLeakParameters) *
        (G.forfeit + G.dropCharge + G.reward / 2) <
      min G.dropCharge G.forfeit - G.reward / 2
  guess_beats_safe :
    G.reward / 2 < lateLeakInclusionProb G.toLateLeakParameters *
        (settleLateLeakProb G * G.reward + (1 - settleLateLeakProb G) * (G.reward / 2)) -
      (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge)

/-- The core packet beats every other packet by a positive margin. -/
theorem SettleLateParameters.DeferralPays.core_gap (pays : G.DeferralPays) (label : LateLeakLabel) :
    settleLateTop G label - min G.dropCharge G.forfeit <
      lateLeakInclusionProb G.toLateLeakParameters * settleLateFloor G label -
        (1 - lateLeakInclusionProb G.toLateLeakParameters) * (G.forfeit + G.dropCharge) := by
  have spread := settleLateTop_sub_floor (G := G) label
  have floor := settleLateFloor_le pays.reward_pos.le label
  have q1 := sub_nonneg.mpr (lateLeakInclusionProb_lt_one G.toLateLeakParameters).le
  have extra := pays.extra_packets
  nlinarith [mul_le_mul_of_nonneg_left floor q1]

/-- A first late turn with the same packet as a plain one is plain. -/
theorem SettleLateFirst.plain_of_packet {first other : SettleLateFirst} (plain : first.Plain)
    (same : other.packet = first.packet) : other.Plain := by
  rcases plain with rfl | ⟨seen, rfl⟩
  · cases other with
    | silent => exact Or.inl rfl
    | signal word => cases same
    | opening seen => cases same
  · cases other with
    | silent => cases same
    | signal word => cases same
    | opening seen' => exact Or.inr ⟨seen', rfl⟩

/-! ## Canonical late histories -/

theorem settleLate_protected_defer_menu (secret : LateLeakType) (early : Option Bool) :
    some (SettleLateMove.emit (settleLateTalkPacket early)) ∈
      settleLateMenu true (settleLateView (SettleLateState.protectedTurn secret).mover
        (.protectedTurn secret)) :=
  ⟨_, rfl, Or.inl rfl⟩

theorem settleLateTalkPacket_ne_opening (early : Option Bool) :
    settleLateTalkPacket early ≠ .opening := by
  cases early <;> simp [settleLateTalkPacket]

/-- The history in which a type defers its protected opening, with an optional
raw signal. -/
def settleLateDeferredHistory (G : SettleLateParameters) (secret : LateLeakType)
    (early : Option Bool) : (settleLateExecution G true).History :=
  settleLateExtend (settleLateTypeHistory G true secret)
    (some (.emit (settleLateTalkPacket early))) (by simp [settleLateTypeHistory_state,
      SettleLateState.IsFinished]) (settleLate_protected_defer_menu secret early)
    (.firstLate secret early) (by
      change _ ∈ (settleLateAdvance G (.protectedTurn secret) _).support
      simp [settleLateAdvance, settleLatePacketOf, settleLateTalkPacket_ne_opening,
        settleLateTalkPacket_word])

theorem settleLateFirstLaw_mem_support (first : SettleLateFirst) :
    first ∈ (settleLateFirstLaw G first.packet).support := by
  cases first with
  | silent => simp [settleLateFirstLaw, SettleLateFirst.packet]
  | signal word => simp [settleLateFirstLaw, SettleLateFirst.packet]
  | opening seen =>
      simp only [settleLateFirstLaw, SettleLateFirst.packet, PMF.support_map]
      exact ⟨seen, (PMF.mem_support_iff _ _).mpr (settleLateLeakCoin_ne_zero seen), rfl⟩

/-- The history reaching the listener's observe-only activation. -/
def settleLateWatchHistory (G : SettleLateParameters) (secret : LateLeakType)
    (early : Option Bool) (first : SettleLateFirst) : (settleLateExecution G true).History :=
  settleLateExtend (settleLateDeferredHistory G secret early) (some (.emit first.packet))
    (by simp [settleLateDeferredHistory, settleLateExtend, SettleLateState.IsFinished])
    ⟨first.packet, rfl⟩ (.watching secret early first) (by
      change _ ∈ (settleLateAdvance G (.firstLate secret early) _).support
      simp only [settleLateAdvance, settleLatePacketOf, PMF.support_map]
      exact ⟨first, settleLateFirstLaw_mem_support first, rfl⟩)

/-- The history reaching the second late turn. -/
def settleLateSecondHistory (G : SettleLateParameters) (secret : LateLeakType)
    (early : Option Bool) (first : SettleLateFirst) (ping : Bool) :
    (settleLateExecution G true).History :=
  settleLateExtend (settleLateWatchHistory G secret early first) (some (.ping ping))
    (by simp [settleLateWatchHistory, settleLateExtend, SettleLateState.IsFinished])
    ⟨ping, rfl⟩ (.secondLate secret early first ping) (by
      change _ ∈ (settleLateAdvance G (.watching secret early first) _).support
      simp [settleLateAdvance, settleLatePingOf])

/-- The history reaching an answer. -/
def settleLateAnswerHistory (G : SettleLateParameters) (record : SettleLateRecord)
    (supported : record.fate ∈ (settleLateFateLaw G record.first record.second).support) :
    (settleLateExecution G true).History :=
  settleLateExtend (settleLateSecondHistory G record.secret record.early record.first record.ping)
    (some (.emit record.second))
    (by simp [settleLateSecondHistory, settleLateExtend, SettleLateState.IsFinished])
    ⟨record.second, rfl⟩ (.answering record) (by
      change _ ∈ (settleLateAdvance G (.secondLate _ _ _ _) _).support
      simp only [settleLateAdvance, settleLatePacketOf, PMF.support_map]
      exact ⟨record.fate, supported, rfl⟩)

theorem settleLate_weight_deferred (profile : SettleLateProfile G true) (secret : LateLeakType)
    (early : Option Bool) :
    (settleLateModel G true).historyReachWeight profile (settleLateDeferredHistory G secret early) =
      lateLeakPrior secret *
        settleLateSenderLaw profile (.protectedTurn secret)
          (some (.emit (settleLateTalkPacket early))) := by
  rw [settleLateDeferredHistory, settleLateExtend_weight, settleLate_weight_type]
  congr 1
  change settleLateSenderLaw profile (.protectedTurn secret)
      (some (.emit (settleLateTalkPacket early))) *
    (settleLateAdvance G (.protectedTurn secret) (some (.emit (settleLateTalkPacket early))))
      (.firstLate secret early) = _
  simp [settleLateAdvance, settleLatePacketOf, settleLateTalkPacket_ne_opening,
    settleLateTalkPacket_word]

theorem settleLate_weight_watch (profile : SettleLateProfile G true) (secret : LateLeakType)
    (early : Option Bool) (first : SettleLateFirst) :
    (settleLateModel G true).historyReachWeight profile
        (settleLateWatchHistory G secret early first) =
      (settleLateModel G true).historyReachWeight profile
          (settleLateDeferredHistory G secret early) *
        (settleLateSenderLaw profile (.firstTurn secret early) (some (.emit first.packet)) *
          settleLateFirstLaw G first.packet first) := by
  rw [settleLateWatchHistory, settleLateExtend_weight]
  congr 2
  change ((settleLateFirstLaw G first.packet).map (SettleLateState.watching secret early))
    (.watching secret early first) = _
  exact pmf_map_apply_of_injective _ (fun _ _ same => by cases same; rfl) _

theorem settleLate_weight_second (profile : SettleLateProfile G true) (secret : LateLeakType)
    (early : Option Bool) (first : SettleLateFirst) (ping : Bool) :
    (settleLateModel G true).historyReachWeight profile
        (settleLateSecondHistory G secret early first ping) =
      (settleLateModel G true).historyReachWeight profile
          (settleLateWatchHistory G secret early first) *
        settleLateListenerLaw profile (.watching early (first.glimpse secret.1))
          (some (.ping ping)) := by
  rw [settleLateSecondHistory, settleLateExtend_weight]
  change _ * (_ * (PMF.pure (SettleLateState.secondLate secret early first ping))
    (.secondLate secret early first ping)) = _
  rw [PMF.pure_apply_self, mul_one]
  rfl

theorem settleLate_weight_answer (profile : SettleLateProfile G true) (record : SettleLateRecord)
    (supported : record.fate ∈ (settleLateFateLaw G record.first record.second).support) :
    (settleLateModel G true).historyReachWeight profile
        (settleLateAnswerHistory G record supported) =
      (settleLateModel G true).historyReachWeight profile
          (settleLateSecondHistory G record.secret record.early record.first record.ping) *
        (settleLateSenderLaw profile
            (.secondTurn record.secret record.early record.first.packet record.ping)
            (some (.emit record.second)) *
          settleLateFateLaw G record.first record.second record.fate) := by
  rw [settleLateAnswerHistory, settleLateExtend_weight]
  congr 2
  change ((settleLateFateLaw G record.first record.second).map fun fate =>
    SettleLateState.answering ⟨record.secret, record.early, record.first, record.ping,
      record.second, fate⟩) (.answering record) = _
  exact pmf_map_apply_of_injective _ (fun _ _ same => by cases same; rfl) _

/-! ## Information sets of the sender -/

theorem settleLate_protectedTurn_fiber {secret : LateLeakType}
    (history : (settleLateModel G late).InformationHistory .sender (.protectedTurn secret)) :
    history.1.state = .protectedTurn secret := by
  have view := settleLate_fiber_view history
  generalize history.1.state = state at view
  cases state <;> simp_all [settleLateView]

theorem settleLate_afterProtected_fiber {secret : LateLeakType}
    (history : (settleLateModel G late).InformationHistory .sender (.afterProtected secret)) :
    history.1.state = .afterProtected secret := by
  have view := settleLate_fiber_view history
  generalize history.1.state = state at view
  cases state <;> simp_all [settleLateView]

theorem settleLate_firstTurn_fiber {secret : LateLeakType} {early : Option Bool}
    (history : (settleLateModel G late).InformationHistory .sender (.firstTurn secret early)) :
    history.1.state = .firstLate secret early := by
  have view := settleLate_fiber_view history
  generalize history.1.state = state at view
  cases state <;> simp_all [settleLateView]

theorem settleLate_secondTurn_fiber {secret : LateLeakType} {early : Option Bool}
    {packet : SettleLatePacket} {ping : Bool}
    (history : (settleLateModel G late).InformationHistory .sender
      (.secondTurn secret early packet ping)) :
    ∃ first : SettleLateFirst, first.packet = packet ∧
      history.1.state = .secondLate secret early first ping := by
  have view := settleLate_fiber_view history
  generalize history.1.state = state at view
  cases state with
  | secondLate secret' early' first ping' =>
      simp only [settleLateView, SettleLateView.secondTurn.injEq] at view
      obtain ⟨rfl, rfl, rfl, rfl⟩ := view
      exact ⟨first, rfl, rfl⟩
  | _ => simp [settleLateView] at view

/-- The sender's information set at its second late turn. -/
def settleLateSecondSite (G : SettleLateParameters) (secret : LateLeakType)
    (early : Option Bool) (first : SettleLateFirst) (ping : Bool) :
    (settleLateModel G true).InformationSite .sender :=
  settleLateSite G true .sender (settleLateSecondHistory G secret early first ping)
    (.emit .silent) ⟨.silent, rfl⟩
    (by simp [settleLateSecondHistory, settleLateExtend, SettleLateState.IsFinished])

/-- The sender's information set at its first late turn. -/
def settleLateFirstSite (G : SettleLateParameters) (secret : LateLeakType)
    (early : Option Bool) : (settleLateModel G true).InformationSite .sender :=
  settleLateSite G true .sender (settleLateDeferredHistory G secret early)
    (.emit .silent) ⟨.silent, rfl⟩
    (by simp [settleLateDeferredHistory, settleLateExtend, SettleLateState.IsFinished])

/-- The sender's information set at its protected turn. -/
def settleLateProtectedSite (G : SettleLateParameters) (late : Bool) (secret : LateLeakType) :
    (settleLateModel G late).InformationSite .sender :=
  settleLateSite G late .sender (settleLateTypeHistory G late secret)
    (.emit .opening) ⟨.opening, rfl, Or.inr rfl⟩
    (by simp [settleLateTypeHistory_state, SettleLateState.IsFinished])

/-! ## The core packet at the second late turn -/

theorem settleLateValue_secondLate_six (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (early : Option Bool)
    (first : SettleLateFirst) (ping : Bool) :
    settleLateValue profile payoff 6 (.secondLate secret early first ping) =
      settleLateSecondValue profile payoff secret early first ping :=
  settleLateValue_secondLate profile payoff 4 secret early first ping

/-- **The core packet at the second late turn.** When the core packet beats
the others, a sequentially rational sender who deferred silently plays it with
probability one, whatever the listener does and believes. -/
theorem settleLate_rational_second_core (pays : G.DeferralPays)
    {A : (settleLateModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G true) (settleLatePayoff G true))
    (secret : LateLeakType) {first : SettleLateFirst} (plain : first.Plain) (ping : Bool) :
    settleLateSenderLaw A.strategy (.secondTurn secret none first.packet ping) =
      PMF.pure (some (.emit (settleLateCorePacket first.packet))) := by
  let site := settleLateSecondSite G secret none first ping
  let core : (settleLateModel G true).Choice .sender site.1 :=
    ⟨some (.emit (settleLateCorePacket first.packet)), ⟨_, rfl⟩⟩
  let deviation := (A.strategy .sender).commit site.1 core
  have optimal := settleLate_rational rational site deviation
  /- The value of each history of the site, by its second late packet. -/
  let settle (state : SettleLateState) (choice : Option SettleLateMove) : ℝ :=
    match state with
    | .secondLate secret early first ping =>
        settleLateSettleValue A.strategy (settleLateStatePayoff G .sender) secret early first ping
          (settleLatePacketOf choice)
    | _ => 0
  have law (profile : SettleLateProfile G true)
      (unchanged : ∀ record, settleLateAnswerValue profile (settleLateStatePayoff G .sender)
        record = settleLateAnswerValue A.strategy (settleLateStatePayoff G .sender) record)
      (history : (settleLateModel G true).InformationHistory .sender site.1) :
      settleLateValue profile (settleLateStatePayoff G .sender) 6 history.1.state =
        expect (settleLateSenderLaw profile site.1) (settle history.1.state) := by
    obtain ⟨first', packet, state⟩ := settleLate_secondTurn_fiber (secret := secret)
      (early := none) (packet := first.packet) (ping := ping) history
    rw [state, settleLateValue_secondLate_six, settleLateSecondValue, packet]
    simp only [settle, settleLateSettleValue, unchanged]
    rfl
  have current := law A.strategy fun _ => rfl
  have deviated := law (settleLateUpdate A.strategy .sender deviation)
    fun record => settleLateAnswerValue_update_sender A.strategy deviation _ record
  have committed : settleLateSenderLaw (settleLateUpdate A.strategy .sender deviation) site.1 =
      PMF.pure core.1 := by
    rw [settleLateSenderLaw_update_sender]
    change (((A.strategy .sender).commit site.1 core) site.1).map Subtype.val = _
    rw [InformationModel.BehavioralPolicy.commit_self (M := settleLateModel G true), PMF.pure_map]
  simp only [current, deviated, committed, expect_pure] at optimal
  apply settleLate_law_eq_pure
  have gap := pays.core_gap secret.2
  refine pmf_apply_eq_one_of_dominant (A.belief .sender site)
    (settleLateSenderLaw A.strategy site.1)
    (fun history => settle history.1.state) core.1 (sub_pos.mpr gap) ?_ optimal
  intro history choice supported different
  obtain ⟨first', packet, state⟩ := settleLate_secondTurn_fiber (secret := secret) (early := none)
    (packet := first.packet) (ping := ping) history
  have plain' : first'.Plain := SettleLateFirst.plain_of_packet plain packet
  obtain ⟨other, rfl⟩ := settleLateSenderLaw_support A.strategy _ choice supported
  have extra := settleLateSettleValue_extra_le A.strategy pays.reward_pos.le
    (by linarith [pays.reward_pos, pays.forfeit_gt]) secret plain' ping other (by
      rw [packet]
      intro same
      exact different (by rw [same]))
  have core_ge := settleLateSettleValue_core_ge A.strategy pays.reward_pos.le
    (by linarith [pays.reward_pos, pays.charge_gt]) secret plain' ping
  rw [packet] at core_ge
  change settle history.1.state (some (.emit other)) + _ ≤ settle history.1.state core.1
  rw [state]
  change settleLateSettleValue A.strategy (settleLateStatePayoff G .sender) secret none first' ping
      other + _ ≤ settleLateSettleValue A.strategy (settleLateStatePayoff G .sender) secret none
      first' ping (settleLateCorePacket first.packet)
  linarith

end Vegas
