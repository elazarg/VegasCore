/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateDeferral

/-! # Consistent beliefs after late inclusions in the settle-late game

Take two types of one class of the committed bit that strictly prefer
opposite late turns after a silent protected turn. Two families of the
listener's information sets matter:

* after an inclusion of serial zero whose opening the observe-only activation
  saw: every history passes the silent deferral and the first-turn opening of
  its type, then the leak, the listener's raw packet and the second turn;
* after an inclusion of serial zero without such a sighting: the same
  first-turn opening missed by the leak, or a hold followed by a second-turn
  opening.

The listener's raw packet is its own move, common to every history of one set,
so it cancels in belief ratios, as does the type's deferral probability.
Along any fully mixed approximation the cross ratio of the two types' beliefs
across one set of each family is then a product of late-turn choice
probabilities, and it vanishes in the limit because the holding type opens at
the first turn with probability tending to zero. Hence one family of sets gives
one of the two types probability zero at every listener packet.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open scoped ENNReal

variable {G : SettleLateParameters} {late : Bool}

/-! ## Reachable answers -/

/-- Only an opening that was emitted can be included. -/
theorem settleLateFateLaw_included_support {first : SettleLateFirst}
    {second : SettleLatePacket} {fate : SettleLateFate}
    (supported : fate ∈ (settleLateFateLaw G first second).support) :
    (fate.included = some .first → first.opened = true) ∧
      (fate.included = some .second → second.isOpening = true) := by
  unfold settleLateFateLaw at supported
  cases opened : first.opened <;> cases opening : second.isOpening <;>
    simp only [opened, opening] at supported
  · rw [PMF.mem_support_pure_iff] at supported
    subst supported
    simp
  · rw [PMF.mem_support_bind_iff] at supported
    obtain ⟨included, _, inner⟩ := supported
    cases included
    · simp only [Bool.false_eq_true, ite_false, PMF.support_map] at inner
      obtain ⟨exposed, _, rfl⟩ := inner
      simp
    · simp only [ite_true, PMF.mem_support_pure_iff] at inner
      subst inner
      simp
  · rw [PMF.mem_support_bind_iff] at supported
    obtain ⟨included, _, inner⟩ := supported
    cases included
    · simp only [Bool.false_eq_true, ite_false, PMF.support_map] at inner
      obtain ⟨exposed, _, rfl⟩ := inner
      simp
    · simp only [ite_true, PMF.mem_support_pure_iff] at inner
      subst inner
      simp
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The inclusion step of a reached answer has positive probability. -/
theorem settleLate_answering_fate_support (history : (settleLateExecution G late).History)
    (record : SettleLateRecord) (state : history.state = .answering record) :
    record.fate ∈ (settleLateFateLaw G record.first record.second).support := by
  rcases history with ⟨current, trace⟩
  change current = _ at state
  cases trace with
  | start => cases state
  | extend prior joint legal realized =>
      subst state
      obtain ⟨parent, jointEq⟩ := settleLate_step_parent legal realized
      change _ ∈ (settleLateAdvance G _ (joint _)).support at realized
      have move := congrFun jointEq (settleLateParent (.answering record)).mover
      rw [settleLateLastJoint_parent_mover] at move
      rw [parent, move] at realized
      simp only [settleLateParent, settleLateLastMove, settleLateAdvance, settleLatePacketOf,
        PMF.support_map] at realized
      obtain ⟨fate, supported, same⟩ := realized
      have fateEq := congrArg SettleLateRecord.fate (SettleLateState.answering.inj same)
      rw [← fateEq]
      exact supported

/-! ## The two families of inclusion sets -/

theorem settleLate_seenSuccess_fiber {bit ping : Bool}
    (history : (settleLateModel G late).InformationHistory .listener
      (.asked (settleLateSeenReport bit ping (some 0)))) :
    ∃ label second, (second = .silent ∨ second = .opening) ∧
      history.1.state = .answering ⟨(bit, label), none, .opening true, ping, second,
        ⟨some .first, false, false⟩⟩ := by
  obtain ⟨record, state, same⟩ := settleLate_asked_fiber history
  rcases record with ⟨⟨secretBit, label⟩, early, first, ping', second, ⟨included, e₁, e₂⟩⟩
  simp only [SettleLateRecord.report, settleLateSeenReport, SettleLateReport.mk.injEq] at same
  obtain ⟨rfl, glimpse, rfl, inclusion, exposed, talk, -⟩ := same
  cases first with
  | silent => simp [SettleLateFirst.glimpse] at glimpse
  | signal word => simp [SettleLateFirst.glimpse] at glimpse
  | opening seen =>
      cases seen
      · simp [SettleLateFirst.glimpse] at glimpse
      · simp only [SettleLateFirst.glimpse, ite_true, SettleLateGlimpse.opening.injEq] at glimpse
        subst glimpse
        cases e₁ <;> cases e₂ <;> simp at exposed
        cases included with
        | none => simp at inclusion
        | some slot =>
            cases slot
            · cases second with
              | silent => exact ⟨label, .silent, Or.inl rfl, state⟩
              | signal word => simp [SettleLatePacket.word] at talk
              | opening => exact ⟨label, .opening, Or.inr rfl, state⟩
            · simp [SettleLateRecord.serial] at inclusion

theorem settleLate_quietSuccess_fiber {bit ping : Bool}
    (history : (settleLateModel G late).InformationHistory .listener
      (.asked (settleLateQuietReport ping (some 0) [] (some bit)))) :
    ∃ label,
      history.1.state = .answering ⟨(bit, label), none, .silent, ping, .opening,
          ⟨some .second, false, false⟩⟩ ∨
        history.1.state = .answering ⟨(bit, label), none, .opening false, ping, .silent,
          ⟨some .first, false, false⟩⟩ ∨
        history.1.state = .answering ⟨(bit, label), none, .opening false, ping, .opening,
          ⟨some .first, false, false⟩⟩ := by
  obtain ⟨record, state, same⟩ := settleLate_asked_fiber history
  have reachable := settleLateFateLaw_included_support
    (settleLate_answering_fate_support history.1 record state)
  rcases record with ⟨⟨secretBit, label⟩, early, first, ping', second, ⟨included, e₁, e₂⟩⟩
  simp only [SettleLateRecord.report, settleLateQuietReport, SettleLateReport.mk.injEq] at same
  obtain ⟨rfl, glimpse, rfl, inclusion, exposed, talk, known⟩ := same
  cases e₁ <;> cases e₂ <;> simp at exposed
  have secretBitEq : secretBit = bit := by
    split at known
    · exact Option.some.inj known
    · cases known
  subst secretBitEq
  refine ⟨label, ?_⟩
  cases second with
  | signal word => simp [SettleLatePacket.word] at talk
  | silent =>
      cases first with
      | silent =>
          cases included with
          | none => simp at inclusion
          | some slot =>
              cases slot
              · simp [SettleLateFirst.opened] at reachable
              · simp [SettleLatePacket.isOpening] at reachable
      | signal word => simp [SettleLateFirst.glimpse] at glimpse
      | opening seen =>
          cases seen
          · cases included with
            | none => simp at inclusion
            | some slot =>
                cases slot
                · exact Or.inr (Or.inl state)
                · simp [SettleLatePacket.isOpening] at reachable
          · simp [SettleLateFirst.glimpse] at glimpse
  | opening =>
      cases first with
      | silent =>
          cases included with
          | none => simp at inclusion
          | some slot =>
              cases slot
              · simp [SettleLateFirst.opened] at reachable
              · exact Or.inl state
      | signal word => simp [SettleLateFirst.glimpse] at glimpse
      | opening seen =>
          cases seen
          · cases included with
            | none => simp at inclusion
            | some slot =>
                cases slot
                · exact Or.inr (Or.inr state)
                · simp [SettleLateRecord.serial] at inclusion
          · simp [SettleLateFirst.glimpse] at glimpse

/-! ## Supported inclusions -/

theorem settleLate_toReal_apply_eq_expect {α : Type*} [DecidableEq α] (law : PMF α) (x : α) :
    (law x).toReal = expect law fun y => if x = y then 1 else 0 := by
  rw [expect_ite_eq, mul_one]

theorem settleLateFateLaw_seenHold_included :
    (settleLateFateLaw G (.opening true) .silent ⟨some .first, false, false⟩).toReal =
      lateLeakInclusionProb G.toLateLeakParameters := by
  rw [settleLate_toReal_apply_eq_expect, settleLate_expect_fate_seenHold]
  simp

theorem settleLateFateLaw_send_included :
    (settleLateFateLaw G .silent .opening ⟨some .second, false, false⟩).toReal =
      lateLeakInclusionProb G.toLateLeakParameters := by
  rw [settleLate_toReal_apply_eq_expect, settleLate_expect_fate_send]
  simp

theorem settleLateFateLaw_unseenHold_included :
    (settleLateFateLaw G (.opening false) .silent ⟨some .first, false, false⟩).toReal =
      lateLeakInclusionProb G.toLateLeakParameters := by
  rw [settleLate_toReal_apply_eq_expect, settleLate_expect_fate_unseenHold]
  simp

theorem settleLateRetryLaw_first_ne_zero : settleLateRetryLaw G (some .first) ≠ 0 := by
  have q0 := lateLeakInclusionProb_pos G.toLateLeakParameters
  simp only [settleLateRetryLaw, PMF.ofFintype_apply, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact div_pos q0 (by linarith)

/-- A retried opening can leave the first-turn opening included and the second
unseen. -/
theorem settleLateFateLaw_retry_first_support (seen : Bool) :
    (⟨some .first, false, false⟩ : SettleLateFate) ∈
      (settleLateFateLaw G (.opening seen) .opening).support := by
  simp only [settleLateFateLaw, SettleLateFirst.opened, SettleLatePacket.isOpening,
    SettleLateFirst.seen]
  rw [PMF.mem_support_bind_iff]
  refine ⟨some .first, (PMF.mem_support_iff _ _).mpr settleLateRetryLaw_first_ne_zero, ?_⟩
  rw [PMF.mem_support_bind_iff]
  refine ⟨false, by simp [settleLateExposure], ?_⟩
  rw [PMF.support_map]
  exact ⟨false, by simpa [settleLateExposure] using
    (PMF.mem_support_iff _ _).mpr (settleLateLeakCoin_ne_zero (G := G) false), rfl⟩

theorem settleLateFateLaw_seenHold_support :
    (⟨some .first, false, false⟩ : SettleLateFate) ∈
      (settleLateFateLaw G (.opening true) .silent).support := by
  apply (PMF.mem_support_iff _ _).mpr
  intro zero
  have := settleLateFateLaw_seenHold_included (G := G)
  rw [zero, ENNReal.toReal_zero] at this
  exact (lateLeakInclusionProb_pos G.toLateLeakParameters).ne this

theorem settleLateFateLaw_send_support :
    (⟨some .second, false, false⟩ : SettleLateFate) ∈
      (settleLateFateLaw G .silent .opening).support := by
  apply (PMF.mem_support_iff _ _).mpr
  intro zero
  have := settleLateFateLaw_send_included (G := G)
  rw [zero, ENNReal.toReal_zero] at this
  exact (lateLeakInclusionProb_pos G.toLateLeakParameters).ne this

theorem settleLateFateLaw_unseenHold_support :
    (⟨some .first, false, false⟩ : SettleLateFate) ∈
      (settleLateFateLaw G (.opening false) .silent).support := by
  apply (PMF.mem_support_iff _ _).mpr
  intro zero
  have := settleLateFateLaw_unseenHold_included (G := G)
  rw [zero, ENNReal.toReal_zero] at this
  exact (lateLeakInclusionProb_pos G.toLateLeakParameters).ne this

/-! ## Sites and members -/

/-- The listener's information set after an inclusion of serial zero whose
opening it saw at its observe-only activation. -/
def settleLateSeenSuccessSite (G : SettleLateParameters) (bit ping : Bool) :
    (settleLateModel G true).InformationSite .listener :=
  settleLateAnswerSite G
    ⟨(bit, .a), none, .opening true, ping, .silent, ⟨some .first, false, false⟩⟩
    settleLateFateLaw_seenHold_support .safe rfl

/-- The listener's information set after an inclusion of serial zero whose
opening it did not see before. -/
def settleLateQuietSuccessSite (G : SettleLateParameters) (bit ping : Bool) :
    (settleLateModel G true).InformationSite .listener :=
  settleLateAnswerSite G
    ⟨(bit, .a), none, .silent, ping, .opening, ⟨some .second, false, false⟩⟩
    settleLateFateLaw_send_support .safe rfl

theorem settleLateSeenSuccessSite_view (bit ping : Bool) :
    (settleLateSeenSuccessSite G bit ping).1 =
      .asked (settleLateSeenReport bit ping (some 0)) := rfl

theorem settleLateQuietSuccessSite_view (bit ping : Bool) :
    (settleLateQuietSuccessSite G bit ping).1 =
      .asked (settleLateQuietReport ping (some 0) [] (some bit)) := rfl

/-- The record of an answer after a deferral without raw signals. -/
def settleLateCoreRecord (secret : LateLeakType) (first : SettleLateFirst) (ping : Bool)
    (second : SettleLatePacket) (included : SettleLateSlot) : SettleLateRecord :=
  ⟨secret, none, first, ping, second, ⟨some included, false, false⟩⟩

/-- A history of a type at a seen inclusion: it holds, or opens again. -/
def settleLateSeenMember (G : SettleLateParameters) (secret : LateLeakType) (ping retry : Bool) :
    (settleLateModel G true).InformationHistory .listener
      (settleLateSeenSuccessSite G secret.1 ping).1 :=
  settleLateMember G true .listener
    (settleLateAnswerHistory G
      (settleLateCoreRecord secret (.opening true) ping (if retry then .opening else .silent)
        .first)
      (by
        cases retry
        · exact settleLateFateLaw_seenHold_support
        · exact settleLateFateLaw_retry_first_support true))
    _ (by cases retry <;> rfl)

/-- How a type reaches an inclusion of serial zero the listener did not see
before: it held and opened at the second turn, or its first-turn opening was
missed and it held or opened again. -/
inductive SettleLateQuietPath
  | send
  | hold
  | retry
  deriving DecidableEq, Fintype

/-- The record of a type's history at an unseen inclusion. -/
def SettleLateQuietPath.record (path : SettleLateQuietPath) (secret : LateLeakType)
    (ping : Bool) : SettleLateRecord :=
  match path with
  | .send => settleLateCoreRecord secret .silent ping .opening .second
  | .hold => settleLateCoreRecord secret (.opening false) ping .silent .first
  | .retry => settleLateCoreRecord secret (.opening false) ping .opening .first

theorem SettleLateQuietPath.supported (path : SettleLateQuietPath) (secret : LateLeakType)
    (ping : Bool) :
    (path.record secret ping).fate ∈
      (settleLateFateLaw G (path.record secret ping).first
        (path.record secret ping).second).support := by
  cases path
  · exact settleLateFateLaw_send_support
  · exact settleLateFateLaw_unseenHold_support
  · exact settleLateFateLaw_retry_first_support false

/-- A history of a type at an unseen inclusion. -/
def settleLateQuietMember (G : SettleLateParameters) (secret : LateLeakType) (ping : Bool)
    (path : SettleLateQuietPath) :
    (settleLateModel G true).InformationHistory .listener
      (settleLateQuietSuccessSite G secret.1 ping).1 :=
  settleLateMember G true .listener
    (settleLateAnswerHistory G (path.record secret ping) (path.supported secret ping))
    _ (by cases path <;> rfl)

/-- Every history of a seen inclusion set is a member of its type. -/
theorem settleLateSeenSuccess_members {bit ping : Bool}
    (history : (settleLateModel G true).InformationHistory .listener
      (settleLateSeenSuccessSite G bit ping).1) :
    ∃ label retry, history = settleLateSeenMember G (bit, label) ping retry := by
  obtain ⟨label, second, opens, state⟩ := settleLate_seenSuccess_fiber
    (late := true) ⟨history.1, history.2.trans (settleLateSeenSuccessSite_view bit ping)⟩
  change history.1.state = _ at state
  rcases opens with rfl | rfl
  · exact ⟨label, false, Subtype.ext (settleLate_history_eq_of_state_eq state)⟩
  · exact ⟨label, true, Subtype.ext (settleLate_history_eq_of_state_eq state)⟩

/-- Every history of an unseen inclusion set is a member of its type. -/
theorem settleLateQuietSuccess_members {bit ping : Bool}
    (history : (settleLateModel G true).InformationHistory .listener
      (settleLateQuietSuccessSite G bit ping).1) :
    ∃ label path, history = settleLateQuietMember G (bit, label) ping path := by
  obtain ⟨label, state⟩ := settleLate_quietSuccess_fiber
    (late := true) ⟨history.1, history.2.trans (settleLateQuietSuccessSite_view bit ping)⟩
  refine ⟨label, ?_⟩
  rcases state with state | state | state
  · exact ⟨.send, Subtype.ext (settleLate_history_eq_of_state_eq state)⟩
  · exact ⟨.hold, Subtype.ext (settleLate_history_eq_of_state_eq state)⟩
  · exact ⟨.retry, Subtype.ext (settleLate_history_eq_of_state_eq state)⟩

/-! ## Weights of the members -/

/-- The probability of the silent deferral of a type, times its prior. -/
def settleLateDeferMass (profile : SettleLateProfile G true) (secret : LateLeakType) : ℝ :=
  (lateLeakPrior secret).toReal *
    (settleLateSenderLaw profile (.protectedTurn secret) (some (.emit .silent))).toReal

/-- The probability of a first-turn packet after a silent deferral. -/
def settleLateFirstMass (profile : SettleLateProfile G true) (secret : LateLeakType)
    (packet : SettleLatePacket) : ℝ :=
  (settleLateSenderLaw profile (.firstTurn secret none) (some (.emit packet))).toReal

/-- The probability of the listener's raw packet at its observe-only
activation after a silent deferral. -/
def settleLatePingMass (profile : SettleLateProfile G true) (glimpse : SettleLateGlimpse)
    (ping : Bool) : ℝ :=
  (settleLateListenerLaw profile (.watching none glimpse) (some (.ping ping))).toReal

/-- The probability of a second-turn packet after a silent deferral. -/
def settleLateSecondMass (profile : SettleLateProfile G true) (secret : LateLeakType)
    (first : SettleLatePacket) (ping : Bool) (packet : SettleLatePacket) : ℝ :=
  (settleLateSenderLaw profile (.secondTurn secret none first ping) (some (.emit packet))).toReal

theorem settleLate_weight_core_toReal (profile : SettleLateProfile G true)
    (secret : LateLeakType) (first : SettleLateFirst) (ping : Bool) (second : SettleLatePacket)
    (included : SettleLateSlot)
    (supported : (settleLateCoreRecord secret first ping second included).fate ∈
      (settleLateFateLaw G first second).support) :
    ((settleLateModel G true).historyReachWeight profile
        (settleLateAnswerHistory G (settleLateCoreRecord secret first ping second included)
          supported)).toReal =
      settleLateDeferMass profile secret *
          (settleLateFirstMass profile secret first.packet *
            (settleLateFirstLaw G first.packet first).toReal) *
        settleLatePingMass profile (first.glimpse secret.1) ping *
        (settleLateSecondMass profile secret first.packet ping second *
          (settleLateFateLaw G first second ⟨some included, false, false⟩).toReal) := by
  rw [settleLate_weight_answer, settleLate_weight_second, settleLate_weight_watch,
    settleLate_weight_deferred]
  simp only [ENNReal.toReal_mul, settleLateDeferMass, settleLateFirstMass, settleLatePingMass,
    settleLateSecondMass, settleLateCoreRecord, settleLateTalkPacket]

/-- What a type's first-turn opening, seen by the leak, contributes at an
inclusion it was seen in, before the listener's raw packet. -/
def settleLateSeenFactor (profile : SettleLateProfile G true) (secret : LateLeakType)
    (ping : Bool) : ℝ :=
  settleLateSecondMass profile secret .opening ping .silent *
      (settleLateFateLaw G (.opening true) .silent ⟨some .first, false, false⟩).toReal +
    settleLateSecondMass profile secret .opening ping .opening *
      (settleLateFateLaw G (.opening true) .opening ⟨some .first, false, false⟩).toReal

/-- What a type's late plans contribute at an unseen inclusion, before the
listener's raw packet. -/
def settleLateQuietFactor (profile : SettleLateProfile G true) (secret : LateLeakType)
    (ping : Bool) : ℝ :=
  settleLateFirstMass profile secret .silent * (settleLateFirstLaw G .silent .silent).toReal *
      (settleLateSecondMass profile secret .silent ping .opening *
        (settleLateFateLaw G .silent .opening ⟨some .second, false, false⟩).toReal) +
    settleLateFirstMass profile secret .opening *
        (settleLateFirstLaw G .opening (.opening false)).toReal *
      (settleLateSecondMass profile secret .opening ping .silent *
          (settleLateFateLaw G (.opening false) .silent ⟨some .first, false, false⟩).toReal +
        settleLateSecondMass profile secret .opening ping .opening *
          (settleLateFateLaw G (.opening false) .opening ⟨some .first, false, false⟩).toReal)

theorem settleLate_seen_weights (profile : SettleLateProfile G true) (secret : LateLeakType)
    (ping : Bool) :
    ((settleLateModel G true).historyReachWeight profile
        (settleLateSeenMember G secret ping false).1).toReal +
      ((settleLateModel G true).historyReachWeight profile
        (settleLateSeenMember G secret ping true).1).toReal =
      settleLateDeferMass profile secret *
        ((settleLateFirstLaw G .opening (.opening true)).toReal *
          settleLatePingMass profile (.opening secret.1) ping *
            (settleLateFirstMass profile secret .opening *
              settleLateSeenFactor profile secret ping)) := by
  simp only [settleLateSeenMember, settleLateMember, Bool.false_eq_true, ite_false, ite_true]
  rw [settleLate_weight_core_toReal, settleLate_weight_core_toReal]
  simp only [SettleLateFirst.packet, SettleLateFirst.glimpse, ite_true, settleLateSeenFactor]
  ring

theorem settleLate_quiet_weights (profile : SettleLateProfile G true) (secret : LateLeakType)
    (ping : Bool) :
    ((settleLateModel G true).historyReachWeight profile
        (settleLateQuietMember G secret ping .send).1).toReal +
      ((settleLateModel G true).historyReachWeight profile
        (settleLateQuietMember G secret ping .hold).1).toReal +
      ((settleLateModel G true).historyReachWeight profile
        (settleLateQuietMember G secret ping .retry).1).toReal =
      settleLateDeferMass profile secret *
        (settleLatePingMass profile .nothing ping * settleLateQuietFactor profile secret ping) := by
  simp only [settleLateQuietMember, settleLateMember, SettleLateQuietPath.record]
  rw [settleLate_weight_core_toReal, settleLate_weight_core_toReal, settleLate_weight_core_toReal]
  simp only [SettleLateFirst.packet, SettleLateFirst.glimpse, Bool.false_eq_true, ite_false,
    settleLateQuietFactor]
  ring

/-! ## Convergence of the factors -/

theorem settleLate_senderLaw_tendsto
    {sequence : ℕ → (settleLateModel G true).BehavioralAssessment}
    {A : (settleLateModel G true).BehavioralAssessment}
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence A)
    (site : (settleLateModel G true).InformationSite .sender) (choice : Option SettleLateMove)
    (menu : choice ∈ settleLateMenu true site.1) :
    Tendsto (fun n => (settleLateSenderLaw (sequence n).strategy site.1 choice).toReal) atTop
      (nhds (settleLateSenderLaw A.strategy site.1 choice).toReal) := by
  simp only [settleLateSenderLaw_apply _ _ _ menu]
  exact (converges.strategy .sender site).toReal ⟨choice, menu⟩

theorem settleLate_listenerLaw_tendsto
    {sequence : ℕ → (settleLateModel G true).BehavioralAssessment}
    {A : (settleLateModel G true).BehavioralAssessment}
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence A)
    (site : (settleLateModel G true).InformationSite .listener) (choice : Option SettleLateMove)
    (menu : choice ∈ settleLateMenu true site.1) :
    Tendsto (fun n => (settleLateListenerLaw (sequence n).strategy site.1 choice).toReal) atTop
      (nhds (settleLateListenerLaw A.strategy site.1 choice).toReal) := by
  simp only [settleLateListenerLaw_apply _ _ _ menu]
  exact (converges.strategy .listener site).toReal ⟨choice, menu⟩

/-- The listener's information set at its observe-only activation. -/
def settleLateWatchSite (G : SettleLateParameters) (secret : LateLeakType)
    (first : SettleLateFirst) : (settleLateModel G true).InformationSite .listener :=
  settleLateSite G true .listener (settleLateWatchHistory G secret none first) (.ping false)
    ⟨false, rfl⟩ (by simp [settleLateWatchHistory, settleLateExtend, SettleLateState.IsFinished])

theorem settleLateFirstMass_tendsto
    {sequence : ℕ → (settleLateModel G true).BehavioralAssessment}
    {A : (settleLateModel G true).BehavioralAssessment}
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence A)
    (secret : LateLeakType) (packet : SettleLatePacket) :
    Tendsto (fun n => settleLateFirstMass (sequence n).strategy secret packet) atTop
      (nhds (settleLateFirstMass A.strategy secret packet)) :=
  settleLate_senderLaw_tendsto converges (settleLateFirstSite G secret none) _ ⟨packet, rfl⟩

theorem settleLateSecondMass_tendsto
    {sequence : ℕ → (settleLateModel G true).BehavioralAssessment}
    {A : (settleLateModel G true).BehavioralAssessment}
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence A)
    (secret : LateLeakType) (first : SettleLateFirst) (ping : Bool) (packet : SettleLatePacket) :
    Tendsto (fun n => settleLateSecondMass (sequence n).strategy secret first.packet ping packet)
      atTop (nhds (settleLateSecondMass A.strategy secret first.packet ping packet)) :=
  settleLate_senderLaw_tendsto converges (settleLateSecondSite G secret none first ping) _
    ⟨packet, rfl⟩

/-! ## The cross ratio -/

/-- The product whose vanishing in the limit forces a face: the first type's
first-turn opening and its contribution at a seen inclusion, and the second
type's contribution at an unseen inclusion. -/
def settleLateCross (profile : SettleLateProfile G true) (sender holder : LateLeakType)
    (seen unseen : Bool) : ℝ :=
  settleLateFirstMass profile sender .opening * settleLateSeenFactor profile sender seen *
    settleLateQuietFactor profile holder unseen

theorem settleLateCross_tendsto
    {sequence : ℕ → (settleLateModel G true).BehavioralAssessment}
    {A : (settleLateModel G true).BehavioralAssessment}
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence A)
    (sender holder : LateLeakType) (seen unseen : Bool) :
    Tendsto (fun n => settleLateCross (sequence n).strategy sender holder seen unseen) atTop
      (nhds (settleLateCross A.strategy sender holder seen unseen)) := by
  have first (secret : LateLeakType) (packet : SettleLatePacket) :=
    settleLateFirstMass_tendsto converges secret packet
  have opened (secret : LateLeakType) (ping : Bool) (packet : SettleLatePacket) :=
    settleLateSecondMass_tendsto converges secret (.opening true) ping packet
  have held (secret : LateLeakType) (ping : Bool) (packet : SettleLatePacket) :=
    settleLateSecondMass_tendsto converges secret .silent ping packet
  simp only [SettleLateFirst.packet] at opened held
  unfold settleLateCross settleLateSeenFactor settleLateQuietFactor
  refine ((first _ _).mul (((opened _ _ _).mul tendsto_const_nhds).add
    ((opened _ _ _).mul tendsto_const_nhds))).mul ?_
  exact (((first _ _).mul tendsto_const_nhds).mul ((held _ _ _).mul tendsto_const_nhds)).add
    (((first _ _).mul tendsto_const_nhds).mul (((opened _ _ _).mul tendsto_const_nhds).add
      ((opened _ _ _).mul tendsto_const_nhds)))

/-! ## Fully mixed approximations -/

theorem settleLate_senderLaw_pos_of_mixed {B : (settleLateModel G true).BehavioralAssessment}
    (mixed : B.IsFullyMixed) (site : (settleLateModel G true).InformationSite .sender)
    (choice : Option SettleLateMove) (menu : choice ∈ settleLateMenu true site.1) :
    0 < (settleLateSenderLaw B.strategy site.1 choice).toReal := by
  refine ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _)
  rw [settleLateSenderLaw_apply _ _ _ menu]
  exact (PMF.mem_support_iff _ _).mp (mixed .sender site ⟨choice, menu⟩)

theorem settleLate_listenerLaw_pos_of_mixed {B : (settleLateModel G true).BehavioralAssessment}
    (mixed : B.IsFullyMixed) (site : (settleLateModel G true).InformationSite .listener)
    (choice : Option SettleLateMove) (menu : choice ∈ settleLateMenu true site.1) :
    0 < (settleLateListenerLaw B.strategy site.1 choice).toReal := by
  refine ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _)
  rw [settleLateListenerLaw_apply _ _ _ menu]
  exact (PMF.mem_support_iff _ _).mp (mixed .listener site ⟨choice, menu⟩)

theorem settleLateDeferMass_pos {B : (settleLateModel G true).BehavioralAssessment}
    (mixed : B.IsFullyMixed) (secret : LateLeakType) :
    0 < settleLateDeferMass B.strategy secret :=
  mul_pos (ENNReal.toReal_pos (lateLeakPrior_ne_zero secret) (PMF.apply_ne_top _ _))
    (settleLate_senderLaw_pos_of_mixed mixed (settleLateProtectedSite G true secret) _
      ⟨.silent, rfl, Or.inl rfl⟩)

theorem settleLateFirstMass_pos {B : (settleLateModel G true).BehavioralAssessment}
    (mixed : B.IsFullyMixed) (secret : LateLeakType) (packet : SettleLatePacket) :
    0 < settleLateFirstMass B.strategy secret packet :=
  settleLate_senderLaw_pos_of_mixed mixed (settleLateFirstSite G secret none) _ ⟨packet, rfl⟩

theorem settleLateSecondMass_pos {B : (settleLateModel G true).BehavioralAssessment}
    (mixed : B.IsFullyMixed) (secret : LateLeakType) (first : SettleLateFirst) (ping : Bool)
    (packet : SettleLatePacket) :
    0 < settleLateSecondMass B.strategy secret first.packet ping packet :=
  settleLate_senderLaw_pos_of_mixed mixed (settleLateSecondSite G secret none first ping) _
    ⟨packet, rfl⟩

theorem settleLatePingMass_pos {B : (settleLateModel G true).BehavioralAssessment}
    (mixed : B.IsFullyMixed) (secret : LateLeakType) (first : SettleLateFirst) (ping : Bool) :
    0 < settleLatePingMass B.strategy (first.glimpse secret.1) ping :=
  settleLate_listenerLaw_pos_of_mixed mixed (settleLateWatchSite G secret first) _ ⟨ping, rfl⟩

theorem settleLate_mass_pos_of_weight {B : (settleLateModel G true).BehavioralAssessment}
    (site : (settleLateModel G true).InformationSite .listener)
    (history : (settleLateModel G true).InformationHistory .listener site.1)
    (positive : 0 < ((settleLateModel G true).historyReachWeight B.strategy history.1).toReal) :
    0 < (settleLateModel G true).informationMass B.strategy .listener site :=
  ((settleLateModel G true).informationMass_pos_iff _ _ _).mpr
    ⟨history, (ENNReal.toReal_pos_iff.mp positive).1⟩

theorem settleLate_belief_toReal {B : (settleLateModel G true).BehavioralAssessment}
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent _ B
      (settleLate_antichain G true))
    (site : (settleLateModel G true).InformationSite .listener)
    (mass : 0 < (settleLateModel G true).informationMass B.strategy .listener site)
    (history : (settleLateModel G true).InformationHistory .listener site.1) :
    (B.belief .listener site history).toReal =
      ((settleLateModel G true).historyReachWeight B.strategy history.1).toReal /
        ((settleLateModel G true).informationMass B.strategy .listener site).toReal := by
  rw [bayes .listener site mass history, ENNReal.toReal_div]

/-! ## The face -/

/-- The belief of a type's histories at a seen inclusion. -/
def settleLateSeenBelief (A : (settleLateModel G true).BehavioralAssessment) (bit : Bool)
    (label : LateLeakLabel) (ping : Bool) : ℝ :=
  (A.belief .listener (settleLateSeenSuccessSite G bit ping)
      (settleLateSeenMember G (bit, label) ping false)).toReal +
    (A.belief .listener (settleLateSeenSuccessSite G bit ping)
      (settleLateSeenMember G (bit, label) ping true)).toReal

/-- The belief of a type's histories at an unseen inclusion. -/
def settleLateQuietBelief (A : (settleLateModel G true).BehavioralAssessment) (bit : Bool)
    (label : LateLeakLabel) (ping : Bool) : ℝ :=
  (A.belief .listener (settleLateQuietSuccessSite G bit ping)
      (settleLateQuietMember G (bit, label) ping .send)).toReal +
    (A.belief .listener (settleLateQuietSuccessSite G bit ping)
      (settleLateQuietMember G (bit, label) ping .hold)).toReal +
    (A.belief .listener (settleLateQuietSuccessSite G bit ping)
      (settleLateQuietMember G (bit, label) ping .retry)).toReal

/-- Along a fully mixed Bayes-consistent assessment, the cross ratio of two
types' beliefs across a seen and an unseen inclusion set is a product of their
late-turn choice probabilities. -/
theorem settleLate_cross_identity {B : (settleLateModel G true).BehavioralAssessment}
    (mixed : B.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent _ B
      (settleLate_antichain G true))
    (bit : Bool) (sender holder : LateLeakLabel) (seen unseen : Bool) :
    settleLateSeenBelief B bit holder seen * settleLateQuietBelief B bit sender unseen *
        settleLateCross B.strategy (bit, sender) (bit, holder) seen unseen =
      settleLateSeenBelief B bit sender seen * settleLateQuietBelief B bit holder unseen *
        settleLateCross B.strategy (bit, holder) (bit, sender) seen unseen := by
  let seenSite := settleLateSeenSuccessSite G bit seen
  let quietSite := settleLateQuietSuccessSite G bit unseen
  have seenMass : 0 < (settleLateModel G true).informationMass B.strategy .listener seenSite := by
    apply settleLate_mass_pos_of_weight seenSite (settleLateSeenMember G (bit, sender) seen false)
    simp only [settleLateSeenMember, settleLateMember, Bool.false_eq_true, ite_false]
    rw [settleLate_weight_core_toReal]
    have coin : 0 < (settleLateFirstLaw G SettleLatePacket.opening (.opening true)).toReal := by
      simp only [settleLateFirstLaw]
      rw [pmf_map_apply_of_injective _ (fun _ _ same => by cases same; rfl),
        settleLateLeakCoin_true]
      exact settleLateLeakProb_pos G
    have fate := settleLateFateLaw_seenHold_included (G := G)
    simp only [SettleLateFirst.packet] at fate ⊢
    rw [fate]
    exact mul_pos (mul_pos (mul_pos (settleLateDeferMass_pos mixed _)
      (mul_pos (settleLateFirstMass_pos mixed _ _) coin))
      (settleLatePingMass_pos mixed (bit, sender) (.opening true) seen))
      (mul_pos (settleLateSecondMass_pos mixed _ (.opening true) _ _)
        (lateLeakInclusionProb_pos G.toLateLeakParameters))
  have quietMass : 0 < (settleLateModel G true).informationMass B.strategy .listener quietSite := by
    apply settleLate_mass_pos_of_weight quietSite
      (settleLateQuietMember G (bit, holder) unseen .send)
    simp only [settleLateQuietMember, settleLateMember, SettleLateQuietPath.record]
    rw [settleLate_weight_core_toReal]
    have fate := settleLateFateLaw_send_included (G := G)
    have stay : (settleLateFirstLaw G SettleLatePacket.silent .silent).toReal = 1 := by
      simp [settleLateFirstLaw]
    simp only [SettleLateFirst.packet] at fate stay ⊢
    rw [fate, stay, mul_one]
    exact mul_pos (mul_pos (mul_pos (settleLateDeferMass_pos mixed _)
      (settleLateFirstMass_pos mixed _ _))
      (settleLatePingMass_pos mixed (bit, holder) .silent unseen))
      (mul_pos (settleLateSecondMass_pos mixed _ .silent _ _)
        (lateLeakInclusionProb_pos G.toLateLeakParameters))
  have seenSum (label : LateLeakLabel) :
      settleLateSeenBelief B bit label seen =
        (settleLateDeferMass B.strategy (bit, label) *
          ((settleLateFirstLaw G .opening (.opening true)).toReal *
            settleLatePingMass B.strategy (.opening bit) seen *
              (settleLateFirstMass B.strategy (bit, label) .opening *
                settleLateSeenFactor B.strategy (bit, label) seen))) /
          ((settleLateModel G true).informationMass B.strategy .listener seenSite).toReal := by
    rw [settleLateSeenBelief, settleLate_belief_toReal bayes seenSite seenMass,
      settleLate_belief_toReal bayes seenSite seenMass, ← add_div,
      settleLate_seen_weights]
  have quietSum (label : LateLeakLabel) :
      settleLateQuietBelief B bit label unseen =
        (settleLateDeferMass B.strategy (bit, label) *
          (settleLatePingMass B.strategy .nothing unseen *
            settleLateQuietFactor B.strategy (bit, label) unseen)) /
          ((settleLateModel G true).informationMass B.strategy .listener quietSite).toReal := by
    rw [settleLateQuietBelief, settleLate_belief_toReal bayes quietSite quietMass,
      settleLate_belief_toReal bayes quietSite quietMass,
      settleLate_belief_toReal bayes quietSite quietMass, ← add_div, ← add_div,
      settleLate_quiet_weights]
  rw [seenSum, seenSum, quietSum, quietSum]
  simp only [settleLateCross]
  ring

/-- **The face.** If one type of a class opens at the first late turn after a
silent deferral and another holds, and both play the core packet at the
second turn, then every consistent assessment gives the holding type
probability zero at every seen inclusion of the class, or the opening type
probability zero at every unseen inclusion of the class. -/
theorem settleLate_consistent_face {A : (settleLateModel G true).BehavioralAssessment}
    (consistent : A.IsSequentiallyConsistent (settleLate_antichain G true)) (bit : Bool)
    (sender holder : LateLeakLabel)
    (sends : settleLateSenderLaw A.strategy (.firstTurn (bit, sender) none) =
      PMF.pure (some (.emit .opening)))
    (holds : settleLateSenderLaw A.strategy (.firstTurn (bit, holder) none) =
      PMF.pure (some (.emit .silent)))
    (senderCore : SettleLateCorePlay A.strategy (bit, sender))
    (holderCore : SettleLateCorePlay A.strategy (bit, holder)) :
    (∀ seen (history : (settleLateModel G true).InformationHistory .listener
        (settleLateSeenSuccessSite G bit seen).1) (record : SettleLateRecord),
        history.1.state = .answering record → record.secret.2 = holder →
          A.belief .listener (settleLateSeenSuccessSite G bit seen) history = 0) ∨
      (∀ unseen (history : (settleLateModel G true).InformationHistory .listener
          (settleLateQuietSuccessSite G bit unseen).1) (record : SettleLateRecord),
          history.1.state = .answering record → record.secret.2 = sender →
            A.belief .listener (settleLateQuietSuccessSite G bit unseen) history = 0) := by
  obtain ⟨sequence, approximate, converges⟩ := consistent
  /- The limit of the cross ratio. -/
  have seenLimit (label : LateLeakLabel) (seen : Bool) :
      Tendsto (fun n => settleLateSeenBelief (sequence n) bit label seen) atTop
        (nhds (settleLateSeenBelief A bit label seen)) :=
    ((converges.belief .listener _).toReal _).add ((converges.belief .listener _).toReal _)
  have quietLimit (label : LateLeakLabel) (unseen : Bool) :
      Tendsto (fun n => settleLateQuietBelief (sequence n) bit label unseen) atTop
        (nhds (settleLateQuietBelief A bit label unseen)) :=
    (((converges.belief .listener _).toReal _).add ((converges.belief .listener _).toReal _)).add
      ((converges.belief .listener _).toReal _)
  have pureMass (view : SettleLateView) (choice other : Option SettleLateMove)
      (law : settleLateSenderLaw A.strategy view = PMF.pure choice) :
      (settleLateSenderLaw A.strategy view other).toReal = if other = choice then 1 else 0 := by
    rw [law, PMF.pure_apply]
    split <;> simp
  have crossSender (seen unseen : Bool) :
      settleLateCross A.strategy (bit, sender) (bit, holder) seen unseen =
        lateLeakInclusionProb G.toLateLeakParameters *
          lateLeakInclusionProb G.toLateLeakParameters := by
    simp only [settleLateCross, settleLateSeenFactor, settleLateQuietFactor, settleLateFirstMass,
      settleLateSecondMass, pureMass _ _ _ sends, pureMass _ _ _ holds,
      pureMass _ _ _ (senderCore seen).2, pureMass _ _ _ (holderCore unseen).1,
      settleLateFateLaw_seenHold_included, settleLateFateLaw_send_included]
    simp [settleLateFirstLaw]
  have crossHolder (seen unseen : Bool) :
      settleLateCross A.strategy (bit, holder) (bit, sender) seen unseen = 0 := by
    simp only [settleLateCross, settleLateFirstMass, pureMass _ _ _ holds]
    simp
  have key (seen unseen : Bool) :
      settleLateSeenBelief A bit holder seen * settleLateQuietBelief A bit sender unseen = 0 := by
    have left := ((seenLimit holder seen).mul (quietLimit sender unseen)).mul
      (settleLateCross_tendsto converges (bit, sender) (bit, holder) seen unseen)
    have right := ((seenLimit sender seen).mul (quietLimit holder unseen)).mul
      (settleLateCross_tendsto converges (bit, holder) (bit, sender) seen unseen)
    have same : (fun n => settleLateSeenBelief (sequence n) bit holder seen *
          settleLateQuietBelief (sequence n) bit sender unseen *
          settleLateCross (sequence n).strategy (bit, sender) (bit, holder) seen unseen) =
        fun n => settleLateSeenBelief (sequence n) bit sender seen *
          settleLateQuietBelief (sequence n) bit holder unseen *
          settleLateCross (sequence n).strategy (bit, holder) (bit, sender) seen unseen := by
      funext n
      exact settleLate_cross_identity (approximate n).1 (approximate n).2 bit sender holder
        seen unseen
    rw [same] at left
    have limits := tendsto_nhds_unique left right
    rw [crossSender, crossHolder, mul_zero] at limits
    have q0 := (lateLeakInclusionProb_pos G.toLateLeakParameters).ne'
    rcases mul_eq_zero.mp limits with zero | zero
    · exact zero
    · exact absurd zero (mul_ne_zero q0 q0)
  /- The dichotomy. -/
  have seenNonneg (label : LateLeakLabel) (seen : Bool) (retry : Bool) :
      0 ≤ (A.belief .listener (settleLateSeenSuccessSite G bit seen)
        (settleLateSeenMember G (bit, label) seen retry)).toReal := ENNReal.toReal_nonneg
  have quietNonneg (label : LateLeakLabel) (unseen : Bool) (path : SettleLateQuietPath) :
      0 ≤ (A.belief .listener (settleLateQuietSuccessSite G bit unseen)
        (settleLateQuietMember G (bit, label) unseen path)).toReal := ENNReal.toReal_nonneg
  have toZero {x : ℝ≥0∞} (finite : x ≠ ⊤) (zero : x.toReal = 0) : x = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp zero).resolve_right finite
  by_cases everywhere : ∀ seen, settleLateSeenBelief A bit holder seen = 0
  · left
    intro seen history record state label
    obtain ⟨label', retry, rfl⟩ := settleLateSeenSuccess_members history
    have recordEq : record = settleLateCoreRecord (bit, label') (.opening true) seen
        (if retry then .opening else .silent) .first := by
      exact (SettleLateState.answering.inj state).symm
    subst recordEq
    change label' = holder at label
    subst label
    have zero := everywhere seen
    rw [settleLateSeenBelief] at zero
    have each := seenNonneg label' seen retry
    have other := seenNonneg label' seen (!retry)
    apply toZero (PMF.apply_ne_top _ _)
    cases retry <;> simp only [Bool.not_false, Bool.not_true] at other <;> linarith
  · right
    obtain ⟨seen, positive⟩ := not_forall.mp everywhere
    intro unseen history record state label
    obtain ⟨label', path, rfl⟩ := settleLateQuietSuccess_members history
    have recordEq : record = path.record (bit, label') unseen := by
      exact (SettleLateState.answering.inj state).symm
    subst recordEq
    have labelEq : label' = sender := by
      cases path <;> exact label
    subst labelEq
    have zero : settleLateQuietBelief A bit label' unseen = 0 :=
      (mul_eq_zero.mp (key seen unseen)).resolve_left positive
    rw [settleLateQuietBelief] at zero
    have s := quietNonneg label' unseen .send
    have h := quietNonneg label' unseen .hold
    have r := quietNonneg label' unseen .retry
    apply toZero (PMF.apply_ne_top _ _)
    cases path <;> linarith

end Vegas
