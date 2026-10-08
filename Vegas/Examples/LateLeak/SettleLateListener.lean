/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.SettleLateIncentives

/-! # The listener's rational answers in the settle-late game

At each answer the listener faces a decision problem over its belief. Its own
raw packet costs it the same at every history of the information set, so it
shifts every answer's reward alike. After a failure in which it saw the
committed bit it guesses that bit. After an inclusion it guesses the label
whenever its belief leaves out one label: the largest remaining coordinate is
then at least `1/2`, more than the safe answer's `2/5`.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : SettleLateParameters} {late : Bool}

/-- The listener's expected payoff from one answer at an information set. -/
def settleLateAnswerReward (A : (settleLateModel G late).BehavioralAssessment)
    (site : (settleLateModel G late).InformationSite .listener) (answer : LateLeakAnswer) : ℝ :=
  expect (A.belief .listener site) fun history =>
    settleLateStatePayoff G .listener (settleLateAnswered history.1.state (some (.reply answer)))

/-- The histories at which the listener sees a report are answering states
with that report. -/
theorem settleLate_asked_fiber {report : SettleLateReport}
    (history : (settleLateModel G late).InformationHistory .listener (.asked report)) :
    ∃ record, history.1.state = .answering record ∧ record.report = report := by
  have view := settleLate_fiber_view history
  generalize history.1.state = state at view
  cases state with
  | answering record => exact ⟨record, rfl, SettleLateView.asked.inj view⟩
  | _ => simp [settleLateView] at view

/-- The histories at which the listener answers after a protected opening. -/
theorem settleLate_protectedAsked_fiber {bit : Bool} {talk : Option Bool}
    (history : (settleLateModel G late).InformationHistory .listener (.protectedAsked bit talk)) :
    ∃ secret, history.1.state = .protectedAnswer secret talk ∧ secret.1 = bit := by
  have view := settleLate_fiber_view history
  generalize history.1.state = state at view
  cases state with
  | protectedAnswer secret talk' =>
      simp only [settleLateView, SettleLateView.protectedAsked.injEq] at view
      obtain ⟨rfl, rfl⟩ := view
      exact ⟨secret, rfl, rfl⟩
  | _ => simp [settleLateView] at view

theorem settleLate_answer_site_answers (site : (settleLateModel G late).InformationSite .listener)
    (answering : (∃ report, site.1 = .asked report) ∨ ∃ bit talk, site.1 = .protectedAsked bit talk)
    (history : (settleLateModel G late).InformationHistory .listener site.1) :
    history.1.state.answers = true := by
  rcases site with ⟨info, decision⟩
  rcases answering with ⟨report, at_report⟩ | ⟨bit, talk, at_report⟩
  · change info = _ at at_report
    subst at_report
    obtain ⟨record, state, -⟩ := settleLate_asked_fiber history
    rw [state]
    rfl
  · change info = _ at at_report
    subst at_report
    obtain ⟨secret, state, -⟩ := settleLate_protectedAsked_fiber history
    rw [state]
    rfl

theorem settleLateListenerDecision_expectedReward (G : SettleLateParameters) (late : Bool)
    (site : (settleLateModel G late).InformationSite .listener)
    (answers : ∀ history : (settleLateModel G late).InformationHistory .listener site.1,
      history.1.state.answers = true)
    (base : (settleLateModel G late).BehavioralPolicy .listener)
    (A : (settleLateModel G late).BehavioralAssessment)
    (choice : (settleLateModel G late).Choice .listener site.1) (answer : LateLeakAnswer)
    (same : choice.1 = some (.reply answer)) :
    (settleLateListenerDecision G late site answers base).expectedReward A choice =
      settleLateAnswerReward A site answer := by
  simp only [InformationModel.ContinuationDecision.expectedReward,
    InformationModel.ContinuationDecision.posterior, expect_map, settleLateAnswerReward]
  congr 1
  funext history
  simp only [Function.comp_apply, settleLateListenerDecision, same]

/-- A supported answer is at least as good as every other answer. -/
theorem settleLate_listener_support_maximal
    {A : (settleLateModel G late).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G late) (settleLatePayoff G late))
    (site : (settleLateModel G late).InformationSite .listener)
    (answers : ∀ history : (settleLateModel G late).InformationHistory .listener site.1,
      history.1.state.answers = true)
    (answer other : LateLeakAnswer)
    (menuAnswer : some (SettleLateMove.reply answer) ∈ settleLateMenu late site.1)
    (menuOther : some (SettleLateMove.reply other) ∈ settleLateMenu late site.1)
    (supported : settleLateListenerLaw A.strategy site.1 (some (.reply answer)) ≠ 0) :
    settleLateAnswerReward A site other ≤ settleLateAnswerReward A site answer := by
  let problem := settleLateListenerDecision G late site answers (A.strategy .listener)
  have maximal := problem.rational_support_maximal A
    ((A.isSequentiallyRational_iff_with _ _).mp rational)
    ⟨some (.reply answer), menuAnswer⟩ (by
      rw [settleLateListenerLaw_apply _ _ _ menuAnswer] at supported
      exact (PMF.mem_support_iff _ _).mpr supported)
    ⟨some (.reply other), menuOther⟩
  rw [settleLateListenerDecision_expectedReward G late site answers _ A
      ⟨some (.reply answer), menuAnswer⟩ answer rfl,
    settleLateListenerDecision_expectedReward G late site answers _ A
      ⟨some (.reply other), menuOther⟩ other rfl] at maximal
  exact maximal

/-- The cost of the listener's raw packet at a report. -/
def settleLatePacketPenalty (G : SettleLateParameters) (report : SettleLateReport) : ℝ :=
  if report.ping then G.packetCost else 0

/-- An answer's reward at a report is its expected base payoff less the
packet cost. -/
theorem settleLateAnswerReward_eq (A : (settleLateModel G late).BehavioralAssessment)
    (site : (settleLateModel G late).InformationSite .listener) (report : SettleLateReport)
    (at_report : site.1 = .asked report) (answer : LateLeakAnswer) :
    settleLateAnswerReward A site answer =
      expect (A.belief .listener site) (fun history =>
        match history.1.state with
        | .answering record => settleLateListenerBase record.secret record.succeeded answer
        | _ => 0) - settleLatePacketPenalty G report := by
  rw [settleLateAnswerReward, ← expect_constant (A.belief .listener site)
      (settleLatePacketPenalty G report),
    ← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  apply expect_congr_on_support
  intro history _
  obtain ⟨record, state, same⟩ := settleLate_asked_fiber (late := late) (report := report)
    ⟨history.1, history.2.trans at_report⟩
  change history.1.state = _ at state
  rw [state]
  simp [settleLateAnswered, settleLateReplyOf, settleLateStatePayoff, settleLatePacketPenalty,
    ← same, SettleLateRecord.report]

/-! ## Failures with a known bit -/

theorem settleLateBitOneProb_bitZero (profile : SettleLateProfile G late)
    (report : SettleLateReport) (failed : report.included = none) :
    (settleLateListenerLaw profile (.asked report) (some (.reply (.failure false)))).toReal =
      1 - settleLateBitOneProb profile (.asked report) := by
  classical
  have computed := lateLeak_expect_two_point (settleLateListenerLaw profile (.asked report))
    (some (.reply (.failure true)))
    (fun choice => if some (SettleLateMove.reply (.failure false)) = choice then 1 else 0)
    1 (fun choice supported different => by
      obtain ⟨answer, rfl, fits⟩ := settleLateListenerLaw_support profile _ choice supported
      cases answer with
      | failure bit =>
          cases bit
          · simp
          · exact (different rfl).elim
      | _ => simp_all [LateLeakAnswer.fitsOutcome])
  rw [expect_ite_eq] at computed
  simpa [settleLateBitOneProb] using computed

/-- After a failure in which it saw the committed bit, the listener guesses
that bit. -/
theorem settleLate_rational_known_failure {A : (settleLateModel G late).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G late) (settleLatePayoff G late))
    (site : (settleLateModel G late).InformationSite .listener) (report : SettleLateReport)
    (at_report : site.1 = .asked report) (failed : report.included = none) (bit : Bool)
    (known : report.bit = some bit) :
    settleLateBitOneProb A.strategy (.asked report) = if bit then 1 else 0 := by
  have answers := settleLate_answer_site_answers site (Or.inl ⟨report, at_report⟩)
  have reward (guess : Bool) : settleLateAnswerReward A site (.failure guess) =
      (if guess = bit then 1 else 0) - settleLatePacketPenalty G report := by
    rw [settleLateAnswerReward_eq A site report at_report, ← expect_constant
      (A.belief .listener site) (if guess = bit then 1 else 0)]
    congr 1
    apply expect_congr_on_support
    intro history _
    obtain ⟨record, state, same⟩ := settleLate_asked_fiber (late := late) (report := report)
      ⟨history.1, history.2.trans at_report⟩
    change history.1.state = _ at state
    have failure : record.succeeded = false := by
      rw [← settleLateReport_success, same, failed]
      rfl
    have secret : record.secret.1 = bit := by
      rw [← same] at known
      simp only [SettleLateRecord.report] at known
      split at known
      · exact Option.some.inj known
      · cases known
    rw [state]
    simp only [settleLateListenerBase, failure, Bool.false_eq_true, ite_false, secret]
  have menu (guess : Bool) : some (SettleLateMove.reply (.failure guess)) ∈
      settleLateMenu late site.1 := by
    rw [at_report]
    exact ⟨_, rfl, by simp [LateLeakAnswer.fitsOutcome, failed]⟩
  have wrong : settleLateListenerLaw A.strategy (.asked report)
      (some (.reply (.failure (!bit)))) = 0 := by
    by_contra supported
    have maximal := settleLate_listener_support_maximal rational site answers
      (.failure (!bit)) (.failure bit) (menu _) (menu _) (by rwa [at_report])
    rw [reward, reward] at maximal
    cases bit <;> norm_num at maximal
  cases bit
  · simpa [settleLateBitOneProb] using congrArg ENNReal.toReal wrong
  · have zero := settleLateBitOneProb_bitZero A.strategy report failed
    rw [show (!true) = false from rfl] at wrong
    rw [wrong, ENNReal.toReal_zero] at zero
    simp only [ite_true]
    linarith

/-! ## Guessing after an inclusion -/

/-- After a success the safe answer is worth `2/5`, less the packet cost. -/
theorem settleLate_safe_reward (A : (settleLateModel G late).BehavioralAssessment)
    (site : (settleLateModel G late).InformationSite .listener) (report : SettleLateReport)
    (at_report : site.1 = .asked report) (success : report.included.isSome = true) :
    settleLateAnswerReward A site .safe = 2 / 5 - settleLatePacketPenalty G report := by
  rw [settleLateAnswerReward_eq A site report at_report, ← expect_constant
    (A.belief .listener site) (2 / 5)]
  congr 1
  apply expect_congr_on_support
  intro history _
  obtain ⟨record, state, same⟩ := settleLate_asked_fiber (late := late) (report := report)
    ⟨history.1, history.2.trans at_report⟩
  change history.1.state = _ at state
  have succeeded : record.succeeded = true := by
    rw [← settleLateReport_success, same, success]
  rw [state]
  simp only [settleLateListenerBase, succeeded, ite_true]

/-- After a success the three label guesses are worth one in total, less three
packet costs. -/
theorem settleLate_guess_rewards_total (A : (settleLateModel G late).BehavioralAssessment)
    (site : (settleLateModel G late).InformationSite .listener) (report : SettleLateReport)
    (at_report : site.1 = .asked report) (success : report.included.isSome = true) :
    settleLateAnswerReward A site (.guess .a) + settleLateAnswerReward A site (.guess .b) +
      settleLateAnswerReward A site (.guess .c) = 1 - 3 * settleLatePacketPenalty G report := by
  simp only [settleLateAnswerReward_eq A site report at_report]
  rw [show ∀ x y z p : ℝ, x - p + (y - p) + (z - p) = (x + y + z) - 3 * p by intros; ring,
    ← expect_add_of_finite, ← expect_add_of_finite, ← expect_constant (A.belief .listener site) 1]
  congr 1
  apply expect_congr_on_support
  intro history _
  obtain ⟨record, state, same⟩ := settleLate_asked_fiber (late := late) (report := report)
    ⟨history.1, history.2.trans at_report⟩
  change history.1.state = _ at state
  have succeeded : record.succeeded = true := by
    rw [← settleLateReport_success, same, success]
  rw [state]
  simp only [settleLateListenerBase, succeeded, ite_true]
  rcases record.secret with ⟨bit, own⟩
  cases own <;> norm_num

/-- The reward of guessing a label whose histories all have belief zero is
minus the packet cost. -/
theorem settleLate_guess_reward_excluded (A : (settleLateModel G late).BehavioralAssessment)
    (site : (settleLateModel G late).InformationSite .listener) (report : SettleLateReport)
    (at_report : site.1 = .asked report) (success : report.included.isSome = true)
    (label : LateLeakLabel)
    (excluded : ∀ (history : (settleLateModel G late).InformationHistory .listener site.1)
      (record : SettleLateRecord), history.1.state = .answering record →
        record.secret.2 = label → A.belief .listener site history = 0) :
    settleLateAnswerReward A site (.guess label) = -settleLatePacketPenalty G report := by
  rw [settleLateAnswerReward_eq A site report at_report,
    show -settleLatePacketPenalty G report = expect (A.belief .listener site) (fun _ => (0 : ℝ)) -
      settleLatePacketPenalty G report by rw [expect_constant]; ring]
  congr 1
  apply expect_congr_on_support
  intro history supported
  obtain ⟨record, state, same⟩ := settleLate_asked_fiber (late := late) (report := report)
    ⟨history.1, history.2.trans at_report⟩
  change history.1.state = _ at state
  have succeeded : record.succeeded = true := by
    rw [← settleLateReport_success, same, success]
  have other : record.secret.2 ≠ label := fun same =>
    ((PMF.mem_support_iff _ _).mp supported) (excluded history record state same)
  rw [state]
  simp only [settleLateListenerBase, succeeded, ite_true]
  simp [Ne.symm other]

/-- After a success, a belief leaving out one label makes the listener
guess. -/
theorem settleLate_rational_guesses {A : (settleLateModel G late).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (settleLate_terminates G late) (settleLatePayoff G late))
    (site : (settleLateModel G late).InformationSite .listener) (report : SettleLateReport)
    (at_report : site.1 = .asked report) (success : report.included.isSome = true)
    (label : LateLeakLabel)
    (excluded : ∀ (history : (settleLateModel G late).InformationHistory .listener site.1)
      (record : SettleLateRecord), history.1.state = .answering record →
        record.secret.2 = label → A.belief .listener site history = 0) :
    settleLateSafeProb A.strategy (.asked report) = 0 := by
  have answers := settleLate_answer_site_answers site (Or.inl ⟨report, at_report⟩)
  by_contra positive
  have supported : settleLateListenerLaw A.strategy site.1 (some (.reply .safe)) ≠ 0 := by
    intro zero
    rw [at_report] at zero
    exact positive (by rw [settleLateSafeProb, zero, ENNReal.toReal_zero])
  have menu (answer : LateLeakAnswer) (fits : answer.fitsOutcome true = true) :
      some (SettleLateMove.reply answer) ∈ settleLateMenu late site.1 := by
    rw [at_report]
    exact ⟨answer, rfl, by rw [success]; exact fits⟩
  have bound (other : LateLeakLabel) :
      settleLateAnswerReward A site (.guess other) ≤ 2 / 5 - settleLatePacketPenalty G report :=
    settleLate_safe_reward A site report at_report success ▸
      settleLate_listener_support_maximal rational site answers .safe (.guess other)
        (menu _ rfl) (menu _ rfl) supported
  have total := settleLate_guess_rewards_total A site report at_report success
  have zero := settleLate_guess_reward_excluded A site report at_report success label excluded
  have ba := bound .a
  have bb := bound .b
  have bc := bound .c
  cases label <;> rw [zero] at total <;> linarith

end Vegas
