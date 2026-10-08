/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateGame
import Vegas.Examples.LateLeak.Play

/-! # Play of the settle-late game

Information states are functions of execution states, so behavioral play of
the settle-late game forgets its history: the state law of play is the
iterated state kernel of the profile. This file computes continuation values
stage by stage, the mass of one kernel step, canonical histories, and the
reduction of sequential rationality to these values.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : SettleLateParameters} {late : Bool}

/-- A behavioral profile of the settle-late game. -/
abbrev SettleLateProfile (G : SettleLateParameters) (late : Bool) : Type :=
  (who : LateLeakRole) → (settleLateModel G late).BehavioralPolicy who

/-- Replace one player's policy in a profile. -/
abbrev settleLateUpdate (profile : SettleLateProfile G late) (who : LateLeakRole)
    (policy : (settleLateModel G late).BehavioralPolicy who) : SettleLateProfile G late :=
  Profile.update (sig := (settleLateModel G late).behavioralSignature) profile who policy

theorem settleLateUpdate_self (profile : SettleLateProfile G late) (who : LateLeakRole) :
    settleLateUpdate profile who (profile who) = profile :=
  Profile.update_eq_self _ _

theorem settleLate_model_infoOf (G : SettleLateParameters) (late : Bool) (who : LateLeakRole)
    {state : SettleLateState} (trace : (settleLateExecution G late).Trace state) :
    (settleLateModel G late).infoOf who trace = settleLateView who state :=
  settleLate_infoOf G late who trace

/-! ## The state kernel -/

/-- The mover's law over its own options at a state. -/
def settleLateMoveLaw (profile : SettleLateProfile G late) (state : SettleLateState) :
    PMF (Option SettleLateMove) :=
  (profile state.mover (settleLateView state.mover state)).map Subtype.val

/-- One step of play from a state. -/
def settleLateKernel (profile : SettleLateProfile G late) (state : SettleLateState) :
    PMF SettleLateState :=
  (settleLateMoveLaw profile state).bind (settleLateAdvance G state)

/-- One step of play from a law over states. -/
def settleLateFlow (profile : SettleLateProfile G late) (law : PMF SettleLateState) :
    PMF SettleLateState :=
  law.bind (settleLateKernel profile)

theorem settleLateFlow_apply (profile : SettleLateProfile G late) (law : PMF SettleLateState) :
    settleLateFlow profile law = law.bind (settleLateKernel profile) := rfl

theorem settleLateFlow_pure (profile : SettleLateProfile G late) (state : SettleLateState) :
    settleLateFlow profile (PMF.pure state) = settleLateKernel profile state :=
  PMF.pure_bind _ _

/-- The behavioral joint law followed by the transition is the state kernel. -/
theorem settleLate_joint_bind_step (profile : SettleLateProfile G late)
    (history : (settleLateExecution G late).History)
    (running : ¬ (settleLateExecution G late).terminal history.state) :
    ((settleLateModel G late).behavioralJoint profile history.trace running).bind
      ((settleLateExecution G late).step history.state) =
        settleLateKernel profile history.state := by
  have unique : ∀ who, (settleLateExecution G late).active history.state who →
      who = history.state.mover := by
    intro who acting
    change history.state.actor = some who at acting
    simp [SettleLateState.mover, acting]
  rw [(settleLateModel G late).behavioralJoint_eq_map_of_at_most_one_active profile history.trace
    running history.state.mover unique, PMF.bind_map]
  calc _ = (profile history.state.mover
        ((settleLateModel G late).infoOf history.state.mover history.trace)).bind
        (fun choice => settleLateAdvance G history.state choice.1) := by
        congr 1
        funext choice
        simp only [Function.comp_apply]
        change settleLateAdvance G history.state
          ((settleLateExecution G late).singletonJoint history.state.mover choice.1
            history.state.mover) = _
        rw [ExecutionProtocol.singletonJoint_self]
    _ = _ := by
        rw [settleLate_model_infoOf, settleLateKernel, settleLateMoveLaw, PMF.bind_map]
        rfl

theorem settleLateKernel_of_finished (profile : SettleLateProfile G late)
    {state : SettleLateState} (stopped : state.IsFinished) :
    settleLateKernel profile state = PMF.pure state := by
  cases state with
  | protectedDone secret talk answer =>
      change (settleLateMoveLaw profile _).bind (fun _ => PMF.pure _) = _
      exact PMF.bind_const _ _
  | finished record answer =>
      change (settleLateMoveLaw profile _).bind (fun _ => PMF.pure _) = _
      exact PMF.bind_const _ _
  | _ => exact stopped.elim

/-- The state law of behavioral play is the iterated state kernel. -/
theorem settleLate_run_map_state (profile : SettleLateProfile G late) (fuel : ℕ)
    (history : (settleLateExecution G late).History) :
    ((settleLateModel G late).runBehavioralFrom profile fuel history).map
        ExecutionProtocol.History.state =
      (settleLateFlow profile)^[fuel] (PMF.pure history.state) := by
  unfold settleLateFlow InformationModel.runBehavioralFrom
  exact ExecutionProtocol.runRandomizedFor_map_state
    ((settleLateModel G late).randomizedChooser profile) (settleLateKernel profile)
    (fun _ stopped => settleLateKernel_of_finished profile stopped)
    (fun history running => settleLate_joint_bind_step profile history running) fuel history

/-- Terminal play has the six-step state law. -/
theorem settleLate_terminal_map_state
    (certificate : (settleLateExecution G late).WellFoundedHistories)
    (profile : SettleLateProfile G late) (history : (settleLateExecution G late).History) :
    ((settleLateModel G late).runBehavioralTerminalFrom certificate profile history).map
        ExecutionProtocol.History.state =
      (settleLateFlow profile)^[6] (PMF.pure history.state) := by
  rw [(settleLateModel G late).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    certificate (settleLate_bounded G late)]
  exact settleLate_run_map_state profile 6 history

theorem settleLateFlow_iterate_eq_bind (profile : SettleLateProfile G late) (fuel : ℕ)
    (law : PMF SettleLateState) :
    (settleLateFlow profile)^[fuel] law =
      law.bind fun state => (settleLateFlow profile)^[fuel] (PMF.pure state) := by
  induction fuel generalizing law with
  | zero => simp only [Function.iterate_zero_apply, PMF.bind_pure]
  | succ fuel ih =>
      rw [Function.iterate_succ_apply, ih, settleLateFlow_apply, PMF.bind_bind]
      congr 1
      funext state
      rw [Function.iterate_succ_apply, settleLateFlow_pure, ih]

/-! ## Values -/

/-- The expected payoff of play from a state after `fuel` steps. -/
def settleLateValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (fuel : ℕ) (state : SettleLateState) : ℝ :=
  expect ((settleLateFlow profile)^[fuel] (PMF.pure state)) payoff

theorem settleLateValue_succ (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (fuel : ℕ) (state : SettleLateState) :
    settleLateValue profile payoff (fuel + 1) state =
      expect (settleLateKernel profile state) (settleLateValue profile payoff fuel) := by
  unfold settleLateValue
  rw [Function.iterate_succ_apply, settleLateFlow_pure, settleLateFlow_iterate_eq_bind,
    expect_bind_of_finite]

theorem settleLateValue_of_finished (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) {state : SettleLateState}
    (stopped : state.IsFinished) :
    settleLateValue profile payoff fuel state = payoff state := by
  induction fuel with
  | zero => simp only [settleLateValue, Function.iterate_zero_apply, expect_pure]
  | succ fuel ih =>
      rw [settleLateValue_succ, settleLateKernel_of_finished profile stopped, expect_pure, ih]

/-- The sender's law over its options at one of its views. -/
def settleLateSenderLaw (profile : SettleLateProfile G late) (view : SettleLateView) :
    PMF (Option SettleLateMove) :=
  (profile .sender view).map Subtype.val

/-- The listener's law over its options at one of its views. -/
def settleLateListenerLaw (profile : SettleLateProfile G late) (view : SettleLateView) :
    PMF (Option SettleLateMove) :=
  (profile .listener view).map Subtype.val

/-- The value of an answering state. -/
def settleLateAnswerValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (record : SettleLateRecord) : ℝ :=
  expect (settleLateListenerLaw profile (.asked record.report)) fun choice =>
    payoff (.finished record (settleLateReplyOf choice))

/-- The value of the inclusion step after the second late packet. -/
def settleLateSettleValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (secret : LateLeakType) (early : Option Bool) (first : SettleLateFirst) (ping : Bool)
    (second : SettleLatePacket) : ℝ :=
  expect (settleLateFateLaw G first second) fun fate =>
    settleLateAnswerValue profile payoff ⟨secret, early, first, ping, second, fate⟩

/-- The value at the second late turn. -/
def settleLateSecondValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (secret : LateLeakType) (early : Option Bool) (first : SettleLateFirst) (ping : Bool) : ℝ :=
  expect (settleLateSenderLaw profile (.secondTurn secret early first.packet ping)) fun choice =>
    settleLateSettleValue profile payoff secret early first ping (settleLatePacketOf choice)

/-- The value at the listener's observe-only activation. -/
def settleLateWatchValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (secret : LateLeakType) (early : Option Bool) (first : SettleLateFirst) : ℝ :=
  expect (settleLateListenerLaw profile (.watching early (first.glimpse secret.1))) fun choice =>
    settleLateSecondValue profile payoff secret early first (settleLatePingOf choice)

/-- The value after the first late packet. -/
def settleLateEmitValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (secret : LateLeakType) (early : Option Bool) (packet : SettleLatePacket) : ℝ :=
  expect (settleLateFirstLaw G packet) fun first =>
    settleLateWatchValue profile payoff secret early first

/-- The value at the first late turn. -/
def settleLateFirstValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (secret : LateLeakType) (early : Option Bool) : ℝ :=
  expect (settleLateSenderLaw profile (.firstTurn secret early)) fun choice =>
    settleLateEmitValue profile payoff secret early (settleLatePacketOf choice)

/-- The value of the listener's answer after a protected opening. -/
def settleLateProtectedAnswerValue (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (talk : Option Bool) : ℝ :=
  expect (settleLateListenerLaw profile (.protectedAsked secret.1 talk)) fun choice =>
    payoff (.protectedDone secret talk (settleLateReplyOf choice))

/-- The value of the sender's activation after a protected opening. -/
def settleLateAfterValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (secret : LateLeakType) : ℝ :=
  expect (settleLateSenderLaw profile (.afterProtected secret)) fun choice =>
    settleLateProtectedAnswerValue profile payoff secret (settleLatePacketOf choice).word

/-- The value of what the sender emits at the protected turn. -/
def settleLateProtectedEmitValue (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (secret : LateLeakType) (packet : SettleLatePacket) : ℝ :=
  if packet = .opening then settleLateAfterValue profile payoff secret
  else settleLateFirstValue profile payoff secret packet.word

/-- The value at the protected turn. -/
def settleLateProtectedValue (profile : SettleLateProfile G late) (payoff : SettleLateState → ℝ)
    (secret : LateLeakType) : ℝ :=
  expect (settleLateSenderLaw profile (.protectedTurn secret)) fun choice =>
    settleLateProtectedEmitValue profile payoff secret (settleLatePacketOf choice)

theorem settleLateValue_answering (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) (record : SettleLateRecord) :
    settleLateValue profile payoff (fuel + 1) (.answering record) =
      settleLateAnswerValue profile payoff record := by
  rw [settleLateValue_succ]
  change expect ((settleLateListenerLaw profile (.asked record.report)).bind
    (settleLateAdvance G (.answering record))) _ = _
  rw [expect_bind_of_finite]
  simp only [settleLateAdvance, expect_pure]
  exact congrArg _ (funext fun choice => settleLateValue_of_finished profile payoff fuel trivial)

theorem settleLateValue_protectedAnswer (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) (secret : LateLeakType) (talk : Option Bool) :
    settleLateValue profile payoff (fuel + 1) (.protectedAnswer secret talk) =
      settleLateProtectedAnswerValue profile payoff secret talk := by
  rw [settleLateValue_succ]
  change expect ((settleLateListenerLaw profile (.protectedAsked secret.1 talk)).bind
    (settleLateAdvance G (.protectedAnswer secret talk))) _ = _
  rw [expect_bind_of_finite]
  simp only [settleLateAdvance, expect_pure]
  exact congrArg _ (funext fun choice => settleLateValue_of_finished profile payoff fuel trivial)

theorem settleLateValue_secondLate (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) (secret : LateLeakType) (early : Option Bool)
    (first : SettleLateFirst) (ping : Bool) :
    settleLateValue profile payoff (fuel + 2) (.secondLate secret early first ping) =
      settleLateSecondValue profile payoff secret early first ping := by
  rw [settleLateValue_succ]
  change expect ((settleLateSenderLaw profile (.secondTurn secret early first.packet ping)).bind
    (settleLateAdvance G (.secondLate secret early first ping))) _ = _
  rw [expect_bind_of_finite]
  simp only [settleLateAdvance, expect_map, Function.comp_def, settleLateValue_answering,
    settleLateSettleValue, settleLateSecondValue]

theorem settleLateValue_watching (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) (secret : LateLeakType) (early : Option Bool)
    (first : SettleLateFirst) :
    settleLateValue profile payoff (fuel + 3) (.watching secret early first) =
      settleLateWatchValue profile payoff secret early first := by
  rw [settleLateValue_succ]
  change expect ((settleLateListenerLaw profile (.watching early (first.glimpse secret.1))).bind
    (settleLateAdvance G (.watching secret early first))) _ = _
  rw [expect_bind_of_finite]
  simp only [settleLateAdvance, expect_pure, settleLateValue_secondLate, settleLateWatchValue]

theorem settleLateValue_firstLate (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) (secret : LateLeakType) (early : Option Bool) :
    settleLateValue profile payoff (fuel + 4) (.firstLate secret early) =
      settleLateFirstValue profile payoff secret early := by
  rw [settleLateValue_succ]
  change expect ((settleLateSenderLaw profile (.firstTurn secret early)).bind
    (settleLateAdvance G (.firstLate secret early))) _ = _
  rw [expect_bind_of_finite]
  simp only [settleLateAdvance, expect_map, Function.comp_def, settleLateValue_watching,
    settleLateEmitValue, settleLateFirstValue]

theorem settleLateValue_afterProtected (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) (secret : LateLeakType) :
    settleLateValue profile payoff (fuel + 2) (.afterProtected secret) =
      settleLateAfterValue profile payoff secret := by
  rw [settleLateValue_succ]
  change expect ((settleLateSenderLaw profile (.afterProtected secret)).bind
    (settleLateAdvance G (.afterProtected secret))) _ = _
  rw [expect_bind_of_finite]
  simp only [settleLateAdvance, expect_pure, settleLateValue_protectedAnswer,
    settleLateAfterValue]

theorem settleLateValue_protectedTurn (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) (secret : LateLeakType) :
    settleLateValue profile payoff (fuel + 5) (.protectedTurn secret) =
      settleLateProtectedValue profile payoff secret := by
  rw [settleLateValue_succ]
  change expect ((settleLateSenderLaw profile (.protectedTurn secret)).bind
    (settleLateAdvance G (.protectedTurn secret))) _ = _
  rw [expect_bind_of_finite]
  simp only [settleLateAdvance, expect_pure, settleLateProtectedValue,
    settleLateProtectedEmitValue]
  congr 1
  funext choice
  split
  · exact settleLateValue_afterProtected profile payoff (fuel + 2) secret
  · exact settleLateValue_firstLate profile payoff fuel secret _

theorem settleLateValue_initial (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) :
    settleLateValue profile payoff (fuel + 6) .initial =
      expect lateLeakPrior fun secret => settleLateProtectedValue profile payoff secret := by
  rw [settleLateValue_succ]
  change expect ((settleLateMoveLaw profile .initial).bind
    fun _ => lateLeakPrior.map SettleLateState.protectedTurn) _ = _
  rw [PMF.bind_const, expect_map]
  simp only [Function.comp_def, settleLateValue_protectedTurn]

/-! ## Updating one player -/

theorem settleLateListenerLaw_update_sender (profile : SettleLateProfile G late)
    (policy : (settleLateModel G late).BehavioralPolicy .sender) (view : SettleLateView) :
    settleLateListenerLaw (settleLateUpdate profile .sender policy) view =
      settleLateListenerLaw profile view := by
  simp only [settleLateListenerLaw, settleLateUpdate, Profile.update_of_ne _ _ (by decide :
    LateLeakRole.listener ≠ LateLeakRole.sender)]

theorem settleLateSenderLaw_update_listener (profile : SettleLateProfile G late)
    (policy : (settleLateModel G late).BehavioralPolicy .listener) (view : SettleLateView) :
    settleLateSenderLaw (settleLateUpdate profile .listener policy) view =
      settleLateSenderLaw profile view := by
  simp only [settleLateSenderLaw, settleLateUpdate, Profile.update_of_ne _ _ (by decide :
    LateLeakRole.sender ≠ LateLeakRole.listener)]

theorem settleLateSenderLaw_update_sender (profile : SettleLateProfile G late)
    (policy : (settleLateModel G late).BehavioralPolicy .sender) (view : SettleLateView) :
    settleLateSenderLaw (settleLateUpdate profile .sender policy) view =
      (policy view).map Subtype.val := by
  simp only [settleLateSenderLaw, settleLateUpdate, Profile.update_same]

theorem settleLateAnswerValue_update_sender (profile : SettleLateProfile G late)
    (policy : (settleLateModel G late).BehavioralPolicy .sender) (payoff : SettleLateState → ℝ)
    (record : SettleLateRecord) :
    settleLateAnswerValue (settleLateUpdate profile .sender policy) payoff record =
      settleLateAnswerValue profile payoff record := by
  simp only [settleLateAnswerValue, settleLateListenerLaw_update_sender]

theorem settleLateSettleValue_update_sender (profile : SettleLateProfile G late)
    (policy : (settleLateModel G late).BehavioralPolicy .sender) (payoff : SettleLateState → ℝ)
    (secret : LateLeakType) (early : Option Bool) (first : SettleLateFirst) (ping : Bool)
    (second : SettleLatePacket) :
    settleLateSettleValue (settleLateUpdate profile .sender policy) payoff secret early first ping
        second =
      settleLateSettleValue profile payoff secret early first ping second := by
  simp only [settleLateSettleValue, settleLateAnswerValue_update_sender]

/-! ## One kernel step -/

/-- The joint action in which the mover plays one option. -/
def settleLateMoverJoint (state : SettleLateState) (choice : Option SettleLateMove) :
    LateLeakRole → Option SettleLateMove :=
  fun who => if who = state.mover then choice else none

theorem settleLate_moverJoint_legal {state : SettleLateState} (running : ¬ state.IsFinished)
    {choice : Option SettleLateMove}
    (menu : choice ∈ settleLateMenu late (settleLateView state.mover state)) :
    (settleLateExecution G late).Legal state (settleLateMoverJoint state choice) := by
  refine ⟨running, (isLegalJoint_iff_legalOption (E := settleLateExecution G late) state
    _).mpr fun who => ?_⟩
  by_cases mover : who = state.mover
  · subst mover
    simp only [settleLateMoverJoint, ite_true]
    exact (settleLate_menu_iff_legal G late _ state choice).mp menu
  · simp only [settleLateMoverJoint, mover, ite_false]
    change ¬ state.actor = some who
    intro acting
    exact mover (by simp [SettleLateState.mover, acting])

theorem settleLateLastJoint_parent_mover (target : SettleLateState) :
    settleLateLastJoint target (settleLateParent target).mover = settleLateLastMove target := by
  cases target <;> simp [settleLateLastJoint, settleLateParent, SettleLateState.mover,
    SettleLateState.actor, settleLateLastMove]

theorem settleLateMoveLaw_menu (profile : SettleLateProfile G late) (state : SettleLateState)
    (choice : Option SettleLateMove)
    (supported : choice ∈ (settleLateMoveLaw profile state).support) :
    choice ∈ settleLateMenu late (settleLateView state.mover state) := by
  rw [settleLateMoveLaw, PMF.mem_support_map_iff] at supported
  obtain ⟨option, _, rfl⟩ := supported
  exact option.2

/-- The kernel mass of a target is the mover's mass at the move leading there,
times the transition mass. -/
theorem settleLateKernel_apply (profile : SettleLateProfile G late) {state : SettleLateState}
    (running : ¬ state.IsFinished) (target : SettleLateState) :
    settleLateKernel profile state target =
      settleLateMoveLaw profile state (settleLateLastMove target) *
        settleLateAdvance G state (settleLateLastMove target) target := by
  rw [settleLateKernel, PMF.bind_apply, tsum_eq_single (settleLateLastMove target)]
  intro choice different
  by_cases supported : choice ∈ (settleLateMoveLaw profile state).support
  · by_cases reached : settleLateAdvance G state choice target = 0
    · rw [reached, mul_zero]
    · exfalso
      have legal := settleLate_moverJoint_legal (G := G) running
        (settleLateMoveLaw_menu profile state choice supported)
      have realized : target ∈ ((settleLateExecution G late).step state ⟨_, legal⟩).support := by
        change target ∈ (settleLateAdvance G state
          (settleLateMoverJoint state choice state.mover)).support
        simp only [settleLateMoverJoint, ite_true]
        exact (PMF.mem_support_iff _ _).mpr reached
      obtain ⟨parent, joint⟩ := settleLate_step_parent legal realized
      have atMover := congrFun joint state.mover
      simp only [settleLateMoverJoint, ite_true] at atMover
      rw [parent, settleLateLastJoint_parent_mover] at atMover
      exact different atMover
  · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul]

/-! ## Reach weights -/

/-- The reach weight of a history is that of its predecessor times one kernel
step. -/
theorem settleLate_reachWeight_step (profile : SettleLateProfile G late)
    (history : (settleLateExecution G late).History) (positive : 0 < history.trace.length) :
    (settleLateModel G late).historyReachWeight profile history =
      (settleLateModel G late).historyReachWeight profile history.prior *
        settleLateKernel profile history.prior.state history.state := by
  rw [(settleLateModel G late).historyReachWeight_eq_prior_mul profile history positive]
  congr 1
  have mapped := settleLate_run_map_state profile 1 history.prior
  have injective := pmf_map_apply_of_injective
    ((settleLateModel G late).runBehavioralFrom profile 1 history.prior)
    (settleLate_state_injective G late) history
  rw [← injective]
  change (PMF.map ExecutionProtocol.History.state
    ((settleLateModel G late).runBehavioralFrom profile 1 history.prior)) history.state = _
  rw [mapped, Function.iterate_one, settleLateFlow_pure]

/-- Extend a history by the mover's option and a realized successor. -/
def settleLateExtend (history : (settleLateExecution G late).History)
    (choice : Option SettleLateMove) (running : ¬ history.state.IsFinished)
    (menu : choice ∈ settleLateMenu late (settleLateView history.state.mover history.state))
    (target : SettleLateState)
    (realized : target ∈ (settleLateAdvance G history.state choice).support) :
    (settleLateExecution G late).History :=
  history.extend (settleLate_moverJoint_legal running menu) (target := target) (by
    change target ∈ (settleLateAdvance G history.state
      (settleLateMoverJoint history.state choice history.state.mover)).support
    simp only [settleLateMoverJoint, ite_true]
    exact realized)

@[simp]
theorem settleLateExtend_state (history : (settleLateExecution G late).History)
    (choice : Option SettleLateMove) (running : ¬ history.state.IsFinished)
    (menu : choice ∈ settleLateMenu late (settleLateView history.state.mover history.state))
    (target : SettleLateState)
    (realized : target ∈ (settleLateAdvance G history.state choice).support) :
    (settleLateExtend history choice running menu target realized).state = target := rfl

theorem settleLateExtend_weight (profile : SettleLateProfile G late)
    (history : (settleLateExecution G late).History)
    (choice : Option SettleLateMove) (running : ¬ history.state.IsFinished)
    (menu : choice ∈ settleLateMenu late (settleLateView history.state.mover history.state))
    (target : SettleLateState)
    (realized : target ∈ (settleLateAdvance G history.state choice).support) :
    (settleLateModel G late).historyReachWeight profile
        (settleLateExtend history choice running menu target realized) =
      (settleLateModel G late).historyReachWeight profile history *
        (settleLateMoveLaw profile history.state (settleLateLastMove target) *
          settleLateAdvance G history.state (settleLateLastMove target) target) := by
  rw [settleLate_reachWeight_step profile (settleLateExtend history choice running menu target
    realized) (Nat.succ_pos _), ← settleLateKernel_apply profile running target]
  rfl

theorem settleLate_reachWeight_init (profile : SettleLateProfile G late) :
    (settleLateModel G late).historyReachWeight profile
      (settleLateExecution G late).initHistory = 1 :=
  (settleLateModel G late).historyReachWeight_initHistory profile

/-! ## Canonical histories -/

theorem settleLatePrior_mem_support (secret : LateLeakType) :
    SettleLateState.protectedTurn secret ∈
      (settleLateAdvance G .initial (none : Option SettleLateMove)).support := by
  rw [settleLateAdvance, PMF.support_map]
  exact ⟨secret, (PMF.mem_support_iff _ _).mpr (lateLeakPrior_ne_zero secret), rfl⟩

/-- The history reaching the protected turn of a type. -/
def settleLateTypeHistory (G : SettleLateParameters) (late : Bool) (secret : LateLeakType) :
    (settleLateExecution G late).History :=
  settleLateExtend (settleLateExecution G late).initHistory none (by
    simp [ExecutionProtocol.initHistory, SettleLateState.IsFinished]) rfl
    (.protectedTurn secret) (settleLatePrior_mem_support secret)

theorem settleLateTypeHistory_state (G : SettleLateParameters) (late : Bool)
    (secret : LateLeakType) :
    (settleLateTypeHistory G late secret).state = .protectedTurn secret := rfl

theorem settleLate_weight_type (profile : SettleLateProfile G late) (secret : LateLeakType) :
    (settleLateModel G late).historyReachWeight profile (settleLateTypeHistory G late secret) =
      lateLeakPrior secret := by
  rw [settleLateTypeHistory, settleLateExtend_weight, settleLate_reachWeight_init, one_mul]
  change settleLateMoveLaw profile .initial none *
    (lateLeakPrior.map SettleLateState.protectedTurn) (.protectedTurn secret) = _
  have total : settleLateMoveLaw profile .initial none = 1 := by
    have only (choice : Option SettleLateMove)
        (supported : choice ∈ (settleLateMoveLaw profile .initial).support) : choice = none :=
      settleLateMoveLaw_menu profile .initial choice supported
    obtain ⟨choice, supported⟩ := (settleLateMoveLaw profile .initial).support_nonempty
    obtain rfl := only choice supported
    exact (PMF.apply_eq_one_iff _ _).mpr (Set.eq_singleton_iff_unique_mem.mpr ⟨supported, only⟩)
  rw [total, one_mul]
  exact pmf_map_apply_of_injective _ (fun _ _ same => SettleLateState.protectedTurn.inj same) _

/-- An information site from a decision history. -/
def settleLateSite (G : SettleLateParameters) (late : Bool) (who : LateLeakRole)
    (history : (settleLateExecution G late).History) (move : SettleLateMove)
    (menu : some move ∈ settleLateMenu late (settleLateView who history.state))
    (running : ¬ history.state.IsFinished) : (settleLateModel G late).InformationSite who :=
  ⟨settleLateView who history.state,
    ⟨⟨history, settleLate_infoOf G late who history.trace⟩, running, move, menu⟩⟩

/-- A history in the information set of a view. -/
def settleLateMember (G : SettleLateParameters) (late : Bool) (who : LateLeakRole)
    (history : (settleLateExecution G late).History) (view : SettleLateView)
    (same : settleLateView who history.state = view) :
    (settleLateModel G late).InformationHistory who view :=
  ⟨history, (settleLate_infoOf G late who history.trace).trans same⟩

theorem settleLate_fiber_view {who : LateLeakRole} {info : SettleLateView}
    (history : (settleLateModel G late).InformationHistory who info) :
    settleLateView who history.1.state = info :=
  (settleLate_infoOf G late who history.1.trace).symm.trans history.2

theorem settleLate_fiber_not_finished {who : LateLeakRole}
    (site : (settleLateModel G late).InformationSite who)
    (history : (settleLateModel G late).InformationHistory who site.1) :
    ¬ history.1.state.IsFinished := by
  obtain ⟨_, _, move, menu⟩ := site.2
  have view := settleLate_fiber_view history
  rw [← view] at menu
  intro finished
  generalize history.1.state = state at menu finished
  cases state <;> cases who <;>
    simp_all [settleLateView, settleLateMenu, SettleLateState.IsFinished]

/-! ## Continuation values and rationality -/

instance (late : Bool) (who : LateLeakRole) (info : SettleLateView) :
    Finite ((settleLateModel G late).InformationHistory who info) :=
  Subtype.finite

/-- A continuation value is the belief average of the six-step value. -/
theorem settleLate_continuation_value (A : (settleLateModel G late).BehavioralAssessment)
    (certificate : (settleLateExecution G late).WellFoundedHistories) {who : LateLeakRole}
    (site : (settleLateModel G late).InformationSite who)
    (alternative : (settleLateModel G late).BehavioralPolicy who) :
    (A.continuationContext certificate site (settleLatePayoff G late who)).value alternative =
      expect (A.belief who site) fun history =>
        settleLateValue (settleLateUpdate A.strategy who alternative)
          (settleLateStatePayoff G who) 6 history.1.state := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, expect_bind_of_finite]
  congr 1
  funext history
  rw [settleLateValue, ← settleLate_terminal_map_state certificate, expect_map]
  rfl

theorem settleLate_context_integrable (A : (settleLateModel G late).BehavioralAssessment)
    (certificate : (settleLateExecution G late).WellFoundedHistories) {who : LateLeakRole}
    (site : (settleLateModel G late).InformationSite who)
    (payoff : (settleLateExecution G late).History → ℝ)
    (alternative : (settleLateModel G late).BehavioralPolicy who) :
    (A.continuationContext certificate site payoff).IntegrableAt alternative :=
  payoffIntegrable_of_finite _ _

/-- Sequential rationality at a site compares belief averages of six-step
values. -/
theorem settleLate_rational {A : (settleLateModel G late).BehavioralAssessment}
    {certificate : (settleLateExecution G late).WellFoundedHistories}
    (rational : A.IsSequentiallyRational certificate (settleLatePayoff G late))
    {who : LateLeakRole} (site : (settleLateModel G late).InformationSite who)
    (alternative : (settleLateModel G late).BehavioralPolicy who) :
    (expect (A.belief who site) fun history =>
        settleLateValue (settleLateUpdate A.strategy who alternative)
          (settleLateStatePayoff G who) 6 history.1.state) ≤
      expect (A.belief who site) fun history =>
        settleLateValue A.strategy (settleLateStatePayoff G who) 6 history.1.state := by
  have optimal := (Context.isLocallyOptimal_iff_of_integrable
    (settleLate_context_integrable A certificate site _ _)
    (fun other _ => settleLate_context_integrable A certificate site _ other)).mp
      (rational who site) alternative (Set.mem_univ _)
  rw [settleLate_continuation_value A certificate site,
    settleLate_continuation_value A certificate site, settleLateUpdate_self] at optimal
  exact optimal

/-- At a site whose histories all reach one state, rationality compares the
six-step values at that state. -/
theorem settleLate_rational_at_state {A : (settleLateModel G late).BehavioralAssessment}
    {certificate : (settleLateExecution G late).WellFoundedHistories}
    (rational : A.IsSequentiallyRational certificate (settleLatePayoff G late))
    {who : LateLeakRole} (site : (settleLateModel G late).InformationSite who)
    {state : SettleLateState}
    (at_state : ∀ history : (settleLateModel G late).InformationHistory who site.1,
      history.1.state = state)
    (alternative : (settleLateModel G late).BehavioralPolicy who) :
    settleLateValue (settleLateUpdate A.strategy who alternative)
        (settleLateStatePayoff G who) 6 state ≤
      settleLateValue A.strategy (settleLateStatePayoff G who) 6 state := by
  have optimal := settleLate_rational rational site alternative
  simp only [at_state, expect_constant] at optimal
  exact optimal

/-- Conversely, comparing six-step values at the common state of a site
establishes rationality there. -/
theorem settleLate_rational_at_state_of_values
    (A : (settleLateModel G late).BehavioralAssessment)
    (certificate : (settleLateExecution G late).WellFoundedHistories)
    {who : LateLeakRole} (site : (settleLateModel G late).InformationSite who)
    {state : SettleLateState}
    (at_state : ∀ history : (settleLateModel G late).InformationHistory who site.1,
      history.1.state = state)
    (values : ∀ alternative : (settleLateModel G late).BehavioralPolicy who,
      settleLateValue (settleLateUpdate A.strategy who alternative)
          (settleLateStatePayoff G who) 6 state ≤
        settleLateValue A.strategy (settleLateStatePayoff G who) 6 state) :
    A.IsSequentiallyRationalAt site
      (A.continuationContext certificate site (settleLatePayoff G late who)) := by
  refine (Context.isLocallyOptimal_iff_of_integrable
    (settleLate_context_integrable A certificate site _ _)
    (fun other _ => settleLate_context_integrable A certificate site _ other)).mpr ?_
  intro alternative _
  rw [settleLate_continuation_value A certificate site,
    settleLate_continuation_value A certificate site, settleLateUpdate_self]
  simp only [at_state, expect_constant]
  exact values alternative

/-! ## The listener's answers -/

/-- Whether the listener answers at a state. -/
def SettleLateState.answers : SettleLateState → Bool
  | .protectedAnswer _ _ | .answering _ => true
  | _ => false

/-- The state an answer leads to. -/
def settleLateAnswered : SettleLateState → Option SettleLateMove → SettleLateState
  | .answering record, choice => .finished record (settleLateReplyOf choice)
  | .protectedAnswer secret talk, choice => .protectedDone secret talk (settleLateReplyOf choice)
  | state, _ => state

theorem settleLateValue_answers (profile : SettleLateProfile G late)
    (payoff : SettleLateState → ℝ) (fuel : ℕ) {state : SettleLateState}
    (answers : state.answers = true) :
    settleLateValue profile payoff (fuel + 1) state =
      expect (settleLateListenerLaw profile (settleLateView .listener state)) fun choice =>
        payoff (settleLateAnswered state choice) := by
  cases state with
  | answering record =>
      rw [settleLateValue_answering]
      rfl
  | protectedAnswer secret talk =>
      rw [settleLateValue_protectedAnswer]
      rfl
  | _ => simp [SettleLateState.answers] at answers

/-- The listener's decision problem at one of its answer sites. -/
def settleLateListenerDecision (G : SettleLateParameters) (late : Bool)
    (site : (settleLateModel G late).InformationSite .listener)
    (answers : ∀ history : (settleLateModel G late).InformationHistory .listener site.1,
      history.1.state.answers = true)
    (base : (settleLateModel G late).BehavioralPolicy .listener) :
    (settleLateModel G late).ContinuationDecision (settleLatePayoff G late)
      ((settleLateModel G late).runBehavioralTerminalFrom (settleLate_terminates G late))
      SettleLateState ((settleLateModel G late).Choice .listener site.1) where
  player := .listener
  site := site
  state history := history.1.state
  response profile := profile .listener site.1
  response_finite _ := Set.toFinite _
  reward state choice := settleLateStatePayoff G .listener (settleLateAnswered state choice.1)
  policy choice := base.commit site.1 choice
  history_value profile history := by
    have mapped := settleLate_terminal_map_state (settleLate_terminates G late) profile history.1
    rw [show (settleLatePayoff G late .listener) =
      (settleLateStatePayoff G .listener) ∘ ExecutionProtocol.History.state from rfl,
      ← expect_map, mapped]
    change settleLateValue profile (settleLateStatePayoff G .listener) (5 + 1)
      history.1.state = _
    rw [settleLateValue_answers profile _ 5 (answers history), settleLateListenerLaw,
      settleLate_fiber_view history, expect_map]
    rfl
  realize profile choice := by
    simp only [Profile.update_same, InformationModel.BehavioralPolicy.commit_self]

end Vegas
