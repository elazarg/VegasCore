/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateOutcome
import Vegas.Examples.LateLeak.SettleLateListener
import Vegas.Examples.LateLeak.SettleLateTurns
import GameTheoryExtensions.Analysis.Protocol.LastDecision
import Mathlib.Probability.Distributions.Uniform

/-! # The intended game of the settle-late game

In the intended game the sender opens at the protected turn and emits nothing
more. The listener's belief after the opening is the prior over labels,
uniform within the committed bit's class, so every label guess is worth `1/3`
while the safe answer is worth `2/5`. The assessment in which the listener
answers safely, with the Bayes beliefs of a uniformly mixed profile, is a
sequential equilibrium, and every sequential equilibrium has the intended
outcome law.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter

variable {G : SettleLateParameters}

/-! ## Play of the intended game -/

/-- In the intended game the sender opens at the protected turn. -/
theorem settleLate_intended_opening (profile : SettleLateProfile G false)
    (secret : LateLeakType) :
    settleLateSenderLaw profile (.protectedTurn secret) = PMF.pure (some (.emit .opening)) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro choice supported
  obtain ⟨packet, rfl, allowed⟩ := settleLateSenderLaw_support profile _ choice supported
  rcases allowed with impossible | rfl
  · cases impossible
  · rfl

/-- In the intended game the sender emits nothing after the protected
opening. -/
theorem settleLate_intended_quiet (profile : SettleLateProfile G false) (secret : LateLeakType) :
    settleLateSenderLaw profile (.afterProtected secret) = PMF.pure (some (.emit .silent)) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro choice supported
  obtain ⟨word, rfl, allowed⟩ := settleLateSenderLaw_support profile _ choice supported
  rcases allowed with impossible | rfl
  · cases impossible
  · rfl

/-- The states the intended game reaches. -/
def SettleLateState.OnIntendedPath : SettleLateState → Prop
  | .initial | .protectedTurn _ | .afterProtected _ => True
  | .protectedAnswer _ talk => talk = none
  | .protectedDone _ talk _ => talk = none
  | _ => False

theorem settleLate_intended_path :
    ∀ {state : SettleLateState} (_ : (settleLateExecution G false).Trace state),
      state.OnIntendedPath
  | _, .start => trivial
  | _, .extend (source := source) (target := target) prior joint legal realized => by
      have earlier := settleLate_intended_path prior
      change target ∈ (settleLateAdvance G source (joint source.mover)).support at realized
      cases source with
      | initial =>
          rw [settleLateAdvance, PMF.support_map] at realized
          obtain ⟨_, _, rfl⟩ := realized
          trivial
      | protectedTurn secret =>
          obtain ⟨move, chosen, menu⟩ :=
            settleLate_mover_choice_of_legal legal (who := .sender) rfl
          obtain ⟨packet, same, allowed⟩ := menu
          obtain rfl := Option.some.inj same
          rcases allowed with impossible | rfl
          · cases impossible
          · simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
              settleLateAdvance, settleLatePacketOf, ite_true, PMF.mem_support_pure_iff] at realized
            subst realized
            trivial
      | afterProtected secret =>
          obtain ⟨move, chosen, menu⟩ :=
            settleLate_mover_choice_of_legal legal (who := .sender) rfl
          obtain ⟨word, same, allowed⟩ := menu
          obtain rfl := Option.some.inj same
          rcases allowed with impossible | rfl
          · cases impossible
          · simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
              settleLateAdvance, settleLatePacketOf, PMF.mem_support_pure_iff] at realized
            subst realized
            rfl
      | protectedAnswer secret talk =>
          simp only [settleLateAdvance, PMF.mem_support_pure_iff] at realized
          subst realized
          exact earlier
      | protectedDone => exact (legal.1 trivial).elim
      | finished => exact (legal.1 trivial).elim
      | _ => exact earlier.elim

/-- The sender's information sets in the intended game are its protected turns
and the activations after them. -/
theorem settleLate_intended_sender_site
    (site : (settleLateModel G false).InformationSite .sender) :
    ∃ secret, site.1 = .protectedTurn secret ∨ site.1 = .afterProtected secret := by
  obtain ⟨history, _, move, menu⟩ := site.2
  have view := settleLate_fiber_view history
  have path := settleLate_intended_path history.1.trace
  rw [← view] at menu ⊢
  generalize history.1.state = state at menu path
  cases state with
  | protectedTurn secret => exact ⟨secret, Or.inl rfl⟩
  | afterProtected secret => exact ⟨secret, Or.inr rfl⟩
  | firstLate => exact path.elim
  | secondLate => exact path.elim
  | _ => simp [settleLateView, settleLateMenu] at menu

/-- The listener's information sets in the intended game follow protected
openings without a raw signal. -/
theorem settleLate_intended_listener_site
    (site : (settleLateModel G false).InformationSite .listener) :
    ∃ bit, site.1 = .protectedAsked bit none := by
  obtain ⟨history, _, move, menu⟩ := site.2
  have view := settleLate_fiber_view history
  have path := settleLate_intended_path history.1.trace
  rw [← view] at menu ⊢
  generalize history.1.state = state at menu path
  cases state with
  | protectedAnswer secret talk =>
      change talk = none at path
      subst path
      exact ⟨secret.1, rfl⟩
  | watching => exact path.elim
  | answering => exact path.elim
  | _ => simp [settleLateView, settleLateMenu] at menu

/-! ## The listener after a protected opening -/

/-- The history in which a type opens at the protected turn. -/
def settleLateOpenedHistory (G : SettleLateParameters) (late : Bool) (secret : LateLeakType) :
    (settleLateExecution G late).History :=
  settleLateExtend (settleLateTypeHistory G late secret) (some (.emit .opening))
    (by simp [settleLateTypeHistory_state, SettleLateState.IsFinished])
    ⟨.opening, rfl, Or.inr rfl⟩ (.afterProtected secret) (by
      change _ ∈ (settleLateAdvance G (.protectedTurn secret) _).support
      simp [settleLateAdvance, settleLatePacketOf])

/-- The history in which a type opens at the protected turn and the listener
is asked without a raw signal. -/
def settleLateProtectedAnswerHistory (G : SettleLateParameters) (late : Bool)
    (secret : LateLeakType) : (settleLateExecution G late).History :=
  settleLateExtend (settleLateOpenedHistory G late secret) (some (.emit .silent))
    (by simp [settleLateOpenedHistory, settleLateExtend, SettleLateState.IsFinished])
    ⟨none, rfl, Or.inr rfl⟩ (.protectedAnswer secret none) (by
      change _ ∈ (settleLateAdvance G (.afterProtected secret) _).support
      simp [settleLateAdvance, settleLatePacketOf, SettleLatePacket.word])

theorem settleLate_weight_opened {late : Bool} (profile : SettleLateProfile G late)
    (secret : LateLeakType) :
    (settleLateModel G late).historyReachWeight profile (settleLateOpenedHistory G late secret) =
      lateLeakPrior secret *
        settleLateSenderLaw profile (.protectedTurn secret) (some (.emit .opening)) := by
  rw [settleLateOpenedHistory, settleLateExtend_weight, settleLate_weight_type]
  congr 1
  change settleLateSenderLaw profile (.protectedTurn secret) (some (.emit .opening)) *
    (settleLateAdvance G (.protectedTurn secret) (some (.emit .opening)))
      (.afterProtected secret) = _
  simp [settleLateAdvance, settleLatePacketOf]

theorem settleLate_intended_weight_answer (profile : SettleLateProfile G false)
    (secret : LateLeakType) :
    (settleLateModel G false).historyReachWeight profile
        (settleLateProtectedAnswerHistory G false secret) = lateLeakPrior secret := by
  rw [settleLateProtectedAnswerHistory, settleLateExtend_weight, settleLate_weight_opened]
  change lateLeakPrior secret * settleLateSenderLaw profile (.protectedTurn secret)
      (some (.emit .opening)) * (settleLateSenderLaw profile (.afterProtected secret)
      (some (.emit .silent)) * (settleLateAdvance G (.afterProtected secret)
        (some (.emit .silent))) (.protectedAnswer secret none)) = _
  rw [settleLate_intended_opening, settleLate_intended_quiet]
  simp [settleLateAdvance, settleLatePacketOf, SettleLatePacket.word]

/-- The history of the intended game in which a type opened, as a history of
the listener's information set. -/
def settleLateOpenedMember (G : SettleLateParameters) (secret : LateLeakType) :
    (settleLateModel G false).InformationHistory .listener (.protectedAsked secret.1 none) :=
  settleLateMember G false .listener (settleLateProtectedAnswerHistory G false secret) _ rfl

theorem settleLate_protectedAsked_members {bit : Bool}
    (history : (settleLateModel G false).InformationHistory .listener (.protectedAsked bit none)) :
    ∃ label, history = settleLateOpenedMember G (bit, label) := by
  obtain ⟨secret, state, same⟩ := settleLate_protectedAsked_fiber history
  obtain ⟨secretBit, label⟩ := secret
  change secretBit = bit at same
  subst same
  exact ⟨label, Subtype.ext (settleLate_history_eq_of_state_eq state)⟩

/-- Bayes' rule after a protected opening gives every label of the class the
same belief. -/
theorem settleLate_intended_bayes_uniform (B : (settleLateModel G false).BehavioralAssessment)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent _ B
      (settleLate_antichain G false)) (bit : Bool)
    (decision : (settleLateModel G false).IsDecisionInfo .listener (.protectedAsked bit none))
    (label other : LateLeakLabel) :
    B.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, label)) =
      B.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, other)) := by
  have mass : 0 < (settleLateModel G false).informationMass B.strategy .listener
      ⟨_, decision⟩ := by
    refine ((settleLateModel G false).informationMass_pos_iff _ _ _).mpr
      ⟨settleLateOpenedMember G (bit, label), ?_⟩
    change 0 < (settleLateModel G false).historyReachWeight B.strategy
      (settleLateProtectedAnswerHistory G false (bit, label))
    rw [settleLate_intended_weight_answer]
    exact pos_iff_ne_zero.mpr (lateLeakPrior_ne_zero _)
  rw [bayes .listener ⟨_, decision⟩ mass, bayes .listener ⟨_, decision⟩ mass]
  change (settleLateModel G false).historyReachWeight B.strategy
      (settleLateProtectedAnswerHistory G false (bit, label)) / _ =
    (settleLateModel G false).historyReachWeight B.strategy
      (settleLateProtectedAnswerHistory G false (bit, other)) / _
  rw [settleLate_intended_weight_answer, settleLate_intended_weight_answer]
  rfl

/-- An answer's reward after a protected opening without a raw signal. -/
theorem settleLate_intended_answerReward (A : (settleLateModel G false).BehavioralAssessment)
    (bit : Bool)
    (decision : (settleLateModel G false).IsDecisionInfo .listener (.protectedAsked bit none))
    (answer : LateLeakAnswer) :
    settleLateAnswerReward A ⟨_, decision⟩ answer =
      expect (A.belief .listener ⟨_, decision⟩) fun history =>
        match history.1.state with
        | .protectedAnswer secret _ => settleLateListenerBase secret true answer
        | _ => 0 := by
  apply expect_congr_on_support
  intro history _
  obtain ⟨secret, state, -⟩ := settleLate_protectedAsked_fiber history
  rw [state]
  rfl

/-- With equal beliefs over labels, every label guess is worth `1/3` and the
safe answer `2/5`. -/
theorem settleLate_intended_rewards (A : (settleLateModel G false).BehavioralAssessment)
    (bit : Bool)
    (decision : (settleLateModel G false).IsDecisionInfo .listener (.protectedAsked bit none))
    (uniform : ∀ label other : LateLeakLabel,
      A.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, label)) =
        A.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, other))) :
    settleLateAnswerReward A ⟨_, decision⟩ .safe = 2 / 5 ∧
      ∀ label, settleLateAnswerReward A ⟨_, decision⟩ (.guess label) = 1 / 3 := by
  classical
  have safe : settleLateAnswerReward A ⟨_, decision⟩ .safe = 2 / 5 := by
    rw [settleLate_intended_answerReward, ← expect_constant (A.belief .listener ⟨_, decision⟩)
      (2 / 5)]
    apply expect_congr_on_support
    intro history _
    obtain ⟨secret, state, -⟩ := settleLate_protectedAsked_fiber history
    simp only [state, settleLateListenerBase, ite_true]
  have guess (label : LateLeakLabel) : settleLateAnswerReward A ⟨_, decision⟩ (.guess label) =
      (A.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, label))).toReal := by
    rw [settleLate_intended_answerReward, ← mul_one (A.belief .listener ⟨_, decision⟩
      (settleLateOpenedMember G (bit, label))).toReal, ← expect_ite_eq]
    apply expect_congr_on_support
    intro history _
    obtain ⟨own, rfl⟩ := settleLate_protectedAsked_members history
    have state : (settleLateOpenedMember G (bit, own)).1.state =
        .protectedAnswer (bit, own) none := rfl
    rw [state]
    simp only [settleLateListenerBase, ite_true]
    by_cases same : label = own
    · subst same
      simp
    · have different :
          settleLateOpenedMember G (bit, label) ≠ settleLateOpenedMember G (bit, own) :=
        fun equal => same (by
          have := congrArg (fun history => history.1.state) equal
          change SettleLateState.protectedAnswer (bit, label) none =
            .protectedAnswer (bit, own) none at this
          exact (Prod.mk.inj (SettleLateState.protectedAnswer.inj this).1).2)
      simp [same, different]
  have total : settleLateAnswerReward A ⟨_, decision⟩ (.guess .a) +
      settleLateAnswerReward A ⟨_, decision⟩ (.guess .b) +
        settleLateAnswerReward A ⟨_, decision⟩ (.guess .c) = 1 := by
    simp only [settleLateAnswerReward]
    rw [← expect_add_of_finite, ← expect_add_of_finite,
      ← expect_constant (A.belief .listener ⟨_, decision⟩) 1]
    apply expect_congr_on_support
    intro history _
    obtain ⟨secret, state, -⟩ := settleLate_protectedAsked_fiber history
    rw [state]
    rcases secret with ⟨secretBit, own⟩
    cases own <;> norm_num [settleLateAnswered, settleLateReplyOf, settleLateStatePayoff,
      settleLateListenerBase]
  refine ⟨safe, fun label => ?_⟩
  have equal (other : LateLeakLabel) := uniform other label
  rw [guess, guess, guess] at total
  rw [guess]
  rw [equal .a, equal .b, equal .c] at total
  linarith

/-! ## The intended outcome -/

theorem settleLateFlow_iterate_protectedDone (profile : SettleLateProfile G false) (fuel : ℕ)
    (secret : LateLeakType) (talk : Option Bool) (answer : LateLeakAnswer) :
    (settleLateFlow profile)^[fuel] (PMF.pure (.protectedDone secret talk answer)) =
      PMF.pure (.protectedDone secret talk answer) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply, settleLateFlow_pure,
        settleLateKernel_of_finished profile (by trivial), ih]

/-- A profile answering safely after every protected opening has the intended
outcome law. -/
theorem settleLateOutcomeLaw_of_safe (profile : SettleLateProfile G false)
    (safe : ∀ bit, settleLateListenerLaw profile (.protectedAsked bit none) =
      PMF.pure (some (.reply .safe))) :
    settleLateOutcomeLaw G false profile = settleLateIntendedOutcome := by
  rw [settleLateOutcomeLaw_eq, Function.iterate_succ_apply, settleLateFlow_pure,
    settleLateFlow_iterate_eq_bind]
  change ((settleLateMoveLaw profile .initial).bind
    fun _ => lateLeakPrior.map SettleLateState.protectedTurn).bind _ = _
  rw [PMF.bind_const, PMF.bind_map, settleLateIntendedOutcome, ← PMF.bind_pure_comp]
  congr 1
  funext secret
  simp only [Function.comp_apply]
  rw [Function.iterate_succ_apply, settleLateFlow_pure]
  change (settleLateFlow profile)^[4] ((settleLateSenderLaw profile (.protectedTurn secret)).bind
    (settleLateAdvance G (.protectedTurn secret))) = _
  rw [settleLate_intended_opening, PMF.pure_bind]
  simp only [settleLateAdvance, settleLatePacketOf, ite_true]
  rw [Function.iterate_succ_apply, settleLateFlow_pure]
  change (settleLateFlow profile)^[3] ((settleLateSenderLaw profile (.afterProtected secret)).bind
    (settleLateAdvance G (.afterProtected secret))) = _
  rw [settleLate_intended_quiet, PMF.pure_bind]
  simp only [settleLateAdvance, settleLatePacketOf, SettleLatePacket.word]
  rw [Function.iterate_succ_apply, settleLateFlow_pure]
  change (settleLateFlow profile)^[2]
    ((settleLateListenerLaw profile (.protectedAsked secret.1 none)).bind
      (settleLateAdvance G (.protectedAnswer secret none))) = _
  rw [safe, PMF.pure_bind]
  simp only [settleLateAdvance, settleLateReplyOf]
  exact settleLateFlow_iterate_protectedDone profile 2 _ _ _

/-! ## An intended sequential equilibrium -/

instance (late : Bool) (who : LateLeakRole) (info : SettleLateView) :
    Finite ((settleLateModel G late).Choice who info) :=
  Subtype.finite

instance (late : Bool) (who : LateLeakRole) (info : SettleLateView) :
    Nonempty ((settleLateModel G late).Choice who info) := by
  change Nonempty {choice // choice ∈ settleLateMenu late info}
  cases info with
  | idle => exact ⟨⟨none, rfl⟩⟩
  | protectedTurn secret => exact ⟨⟨some (.emit .opening), ⟨.opening, rfl, Or.inr rfl⟩⟩⟩
  | afterProtected secret => exact ⟨⟨some (.emit .silent), ⟨none, rfl, Or.inr rfl⟩⟩⟩
  | firstTurn secret early => exact ⟨⟨some (.emit .silent), ⟨.silent, rfl⟩⟩⟩
  | secondTurn secret early first ping => exact ⟨⟨some (.emit .silent), ⟨.silent, rfl⟩⟩⟩
  | watching early glimpse => exact ⟨⟨some (.ping false), ⟨false, rfl⟩⟩⟩
  | protectedAsked bit talk => exact ⟨⟨some (.reply .safe), ⟨.safe, rfl, rfl⟩⟩⟩
  | asked report =>
      by_cases success : report.included.isSome
      · exact ⟨⟨some (.reply .safe), ⟨.safe, rfl, by simpa [LateLeakAnswer.fitsOutcome]⟩⟩⟩
      · exact ⟨⟨some (.reply (.failure true)), ⟨.failure true, rfl, by
          simpa [LateLeakAnswer.fitsOutcome] using success⟩⟩⟩

/-- Every option equally likely at every information state. -/
def settleLateUniformProfile (G : SettleLateParameters) (late : Bool) :
    SettleLateProfile G late := fun _ _ =>
  letI := Fintype.ofFinite
  PMF.uniformOfFintype _

theorem settleLateUniformProfile_mixed (G : SettleLateParameters) (late : Bool)
    (who : LateLeakRole) (site : (settleLateModel G late).InformationSite who)
    (choice : (settleLateModel G late).Choice who site.1) :
    choice ∈ (settleLateUniformProfile G late who site.1).support := by
  let _ := Fintype.ofFinite ((settleLateModel G late).Choice who site.1)
  exact PMF.mem_support_uniformOfFintype choice

/-- The listener's safe answer after every protected opening. -/
def settleLateSafePolicy (G : SettleLateParameters) (late : Bool) :
    (settleLateModel G late).BehavioralPolicy .listener :=
  fun info =>
    match info with
    | .protectedAsked _ _ => PMF.pure ⟨some (.reply .safe), ⟨.safe, rfl, rfl⟩⟩
    | other => settleLateUniformProfile G late .listener other

theorem settleLateKernel_update_listener (profile : SettleLateProfile G false)
    (policy : (settleLateModel G false).BehavioralPolicy .listener) (state : SettleLateState)
    (mover : state.mover = .sender) :
    settleLateKernel (settleLateUpdate profile .listener policy) state =
      settleLateKernel profile state := by
  unfold settleLateKernel settleLateMoveLaw
  rw [mover]
  simp only [settleLateUpdate, Profile.update_of_ne _ _ (by decide :
    LateLeakRole.sender ≠ LateLeakRole.listener)]

/-- The listener's policy does not change the weight of any history before its
answer in the intended game. -/
theorem settleLate_weight_update_listener (profile : SettleLateProfile G false)
    (policy : (settleLateModel G false).BehavioralPolicy .listener) :
    ∀ {state : SettleLateState} (trace : (settleLateExecution G false).Trace state),
      ¬ state.IsFinished →
      (settleLateModel G false).historyReachWeight (settleLateUpdate profile .listener policy)
          ⟨state, trace⟩ =
        (settleLateModel G false).historyReachWeight profile ⟨state, trace⟩
  | _, .start, _ => (settleLate_reachWeight_init _).trans (settleLate_reachWeight_init _).symm
  | _, .extend (source := source) (target := target) prior joint legal realized, running => by
      rw [settleLate_reachWeight_step _ ⟨target, .extend prior joint legal realized⟩
          (Nat.succ_pos _),
        settleLate_reachWeight_step _ ⟨target, .extend prior joint legal realized⟩
          (Nat.succ_pos _)]
      change (settleLateModel G false).historyReachWeight _ ⟨source, prior⟩ *
          settleLateKernel _ source target =
        (settleLateModel G false).historyReachWeight _ ⟨source, prior⟩ *
          settleLateKernel _ source target
      have path := settleLate_intended_path prior
      have mover : source.mover = .sender := by
        change target ∈ (settleLateAdvance G source (joint source.mover)).support at realized
        cases source with
        | protectedAnswer secret talk =>
            simp only [settleLateAdvance, PMF.mem_support_pure_iff] at realized
            subst realized
            exact (running trivial).elim
        | answering record =>
            simp only [settleLateAdvance, PMF.mem_support_pure_iff] at realized
            subst realized
            exact (running trivial).elim
        | watching => exact path.elim
        | _ => rfl
      rw [settleLate_weight_update_listener profile policy prior legal.1,
        settleLateKernel_update_listener profile policy source mover]

/-- The intended sequential equilibrium: the sender opens at the protected
turn, the listener answers safely, and beliefs are the Bayes beliefs of the
uniformly mixed profile. -/
def settleLateIntendedAssessment (G : SettleLateParameters) :
    (settleLateModel G false).BehavioralAssessment :=
  ⟨settleLateUpdate (settleLateUniformProfile G false) .listener (settleLateSafePolicy G false),
    ((settleLateModel G false).bayesAssessment (settleLateUniformProfile G false)
      (settleLateUniformProfile_mixed G false) (settleLate_antichain G false)).belief⟩

theorem settleLateIntendedAssessment_safe (bit : Bool) :
    settleLateListenerLaw (settleLateIntendedAssessment G).strategy (.protectedAsked bit none) =
      PMF.pure (some (.reply .safe)) := by
  simp [settleLateListenerLaw, settleLateIntendedAssessment, settleLateUpdate,
    settleLateSafePolicy, PMF.pure_map]

theorem settleLateIntendedAssessment_isSequentialEquilibrium :
    (settleLateIntendedAssessment G).IsSequentialEquilibrium (settleLate_antichain G false)
      (settleLate_terminates G false) (settleLatePayoff G false) := by
  let reference : (settleLateModel G false).BehavioralAssessment :=
    InformationModel.BehavioralAssessment.ofStrategy (settleLateUniformProfile G false)
  have mixed : reference.IsFullyMixed := settleLateUniformProfile_mixed G false
  refine ⟨?_, ?_⟩
  · intro who site
    cases who with
    | sender =>
        obtain ⟨secret, at_view⟩ := settleLate_intended_sender_site site
        rcases at_view with at_view | at_view
        · apply settleLate_rational_at_state_of_values _ _ site (state := .protectedTurn secret)
            (fun history => settleLate_protectedTurn_fiber ⟨history.1, history.2.trans at_view⟩)
          intro alternative
          rw [show (6 : ℕ) = 1 + 5 from rfl, settleLateValue_protectedTurn,
            settleLateValue_protectedTurn, settleLateProtectedValue, settleLateProtectedValue,
            settleLate_intended_opening, settleLate_intended_opening, expect_pure, expect_pure]
          simp only [settleLatePacketOf, settleLateProtectedEmitValue, ite_true,
            settleLateAfterValue, settleLate_intended_quiet, expect_pure,
            settleLateProtectedAnswerValue, settleLateListenerLaw_update_sender, le_refl]
        · apply settleLate_rational_at_state_of_values _ _ site (state := .afterProtected secret)
            (fun history => settleLate_afterProtected_fiber ⟨history.1, history.2.trans at_view⟩)
          intro alternative
          rw [show (6 : ℕ) = 4 + 2 from rfl, settleLateValue_afterProtected,
            settleLateValue_afterProtected, settleLateAfterValue, settleLateAfterValue,
            settleLate_intended_quiet, settleLate_intended_quiet, expect_pure, expect_pure]
          simp only [settleLateProtectedAnswerValue, settleLateListenerLaw_update_sender, le_refl]
    | listener =>
        obtain ⟨bit, at_view⟩ := settleLate_intended_listener_site site
        rcases site with ⟨info, decision⟩
        change info = _ at at_view
        subst at_view
        have answers := settleLate_answer_site_answers (late := false) ⟨_, decision⟩
          (Or.inr ⟨bit, none, rfl⟩)
        let problem := settleLateListenerDecision G false ⟨_, decision⟩ answers
          (settleLateSafePolicy G false)
        refine (problem.rationalAt_iff_support_maximal (settleLateIntendedAssessment G)).mpr ?_
        intro choice supported other
        have uniform := settleLate_intended_bayes_uniform
          ((settleLateModel G false).bayesAssessment (settleLateUniformProfile G false)
            (settleLateUniformProfile_mixed G false) (settleLate_antichain G false))
          ((settleLateModel G false).bayesAssessment_isBayesConsistent _ _ _) bit decision
        have rewards := settleLate_intended_rewards (settleLateIntendedAssessment G) bit decision
          uniform
        have law : (settleLateIntendedAssessment G).strategy .listener
            (.protectedAsked bit none) = PMF.pure ⟨some (.reply .safe), ⟨.safe, rfl, rfl⟩⟩ := by
          simp [settleLateIntendedAssessment, settleLateUpdate, settleLateSafePolicy]
        change choice ∈ ((settleLateIntendedAssessment G).strategy .listener
          (.protectedAsked bit none)).support at supported
        rw [law, PMF.mem_support_pure_iff] at supported
        subst supported
        obtain ⟨answer, same, fits⟩ := other.2
        rw [settleLateListenerDecision_expectedReward G _ _ _ _ _ other answer same,
          settleLateListenerDecision_expectedReward G _ _ _ _ _ _ .safe rfl, rewards.1]
        cases answer with
        | safe => rw [rewards.1]
        | guess label =>
            rw [rewards.2 label]
            norm_num
        | failure => simp [LateLeakAnswer.fitsOutcome] at fits
  · have reach : ∀ (alternative : (settleLateModel G false).BehavioralPolicy .listener)
        (player : LateLeakRole) (site : (settleLateModel G false).InformationSite player)
        (history : (settleLateModel G false).InformationHistory player site.1),
        (settleLateModel G false).historyReachWeight
          (Profile.update (sig := (settleLateModel G false).behavioralSignature)
            reference.strategy .listener alternative) history.1 =
          (settleLateModel G false).historyReachWeight reference.strategy history.1 :=
      fun alternative player site history =>
        settleLate_weight_update_listener reference.strategy alternative history.1.trace
          (settleLate_fiber_not_finished site history)
    exact InformationModel.consistent_update_of_reach_invariant reference mixed
      (settleLate_antichain G false) .listener reach (settleLateSafePolicy G false)

/-- Every sequential equilibrium of the intended game has the intended outcome
law. -/
theorem settleLate_intended_outcome (A : (settleLateModel G false).BehavioralAssessment)
    (equilibrium : A.IsSequentialEquilibrium (settleLate_antichain G false)
      (settleLate_terminates G false) (settleLatePayoff G false)) :
    settleLateOutcomeLaw G false A.strategy = settleLateIntendedOutcome := by
  obtain ⟨rational, sequence, approximate, converges⟩ := equilibrium
  apply settleLateOutcomeLaw_of_safe
  intro bit
  have decision : (settleLateModel G false).IsDecisionInfo .listener
      (.protectedAsked bit none) :=
    (settleLateSite G false .listener (settleLateProtectedAnswerHistory G false (bit, .a))
      (.reply .safe) ⟨.safe, rfl, rfl⟩
      (by simp [settleLateProtectedAnswerHistory, settleLateExtend,
        SettleLateState.IsFinished])).2
  have uniform (label other : LateLeakLabel) :
      A.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, label)) =
        A.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, other)) := by
    have same (n : ℕ) := settleLate_intended_bayes_uniform (sequence n) (approximate n).2 bit
      decision label other
    have first := converges.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, label))
    have second :=
      converges.belief .listener ⟨_, decision⟩ (settleLateOpenedMember G (bit, other))
    simp only [same] at first
    exact tendsto_nhds_unique first second
  have rewards := settleLate_intended_rewards A bit decision uniform
  have answers := settleLate_answer_site_answers (late := false) ⟨_, decision⟩
    (Or.inr ⟨bit, none, rfl⟩)
  apply pmf_eq_pure_of_support_subset_singleton
  intro choice supported
  obtain ⟨answer, rfl, fits⟩ := settleLateListenerLaw_support A.strategy _ choice supported
  cases answer with
  | safe => rfl
  | guess label =>
      have maximal := settleLate_listener_support_maximal rational ⟨_, decision⟩ answers
        (.guess label) .safe ⟨_, rfl, fits⟩ ⟨_, rfl, rfl⟩ ((PMF.mem_support_iff _ _).mp supported)
      rw [rewards.1, rewards.2 label] at maximal
      norm_num at maximal
  | failure bit => simp [LateLeakAnswer.fitsOutcome] at fits

/-- **The intended game.** It has a sequential equilibrium, and every
sequential equilibrium has the intended outcome law: every type opens at the
protected turn, emits nothing more, and the listener answers safely. -/
theorem settleLate_intended_equilibria (G : SettleLateParameters) :
    (∃ A : (settleLateModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (settleLate_antichain G false) (settleLate_terminates G false)
        (settleLatePayoff G false)) ∧
    ∀ A : (settleLateModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (settleLate_antichain G false) (settleLate_terminates G false)
          (settleLatePayoff G false) →
        settleLateOutcomeLaw G false A.strategy = settleLateIntendedOutcome :=
  ⟨⟨settleLateIntendedAssessment G, settleLateIntendedAssessment_isSequentialEquilibrium⟩,
    settleLate_intended_outcome⟩

end Vegas
