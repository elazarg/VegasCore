/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Incentives

/-! # The listener's rational answers

At each of its information sets the listener faces a decision problem over
the belief of its assessment. After a pending opening failed it knows the
committed bit and guesses it. After a success it guesses the label whenever
its belief leaves out one label: the largest remaining coordinate is then at
least `1/2`, more than the safe answer's `2/5`.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {late : Bool}

/-- The listener's expected payoff from one answer at an information set. -/
def lateLeakAnswerReward (A : (lateLeakModel late).BehavioralAssessment)
    (site : (lateLeakModel late).InformationSite .listener) (answer : LateLeakAnswer) : ℝ :=
  expect (A.belief .listener site) fun history =>
    lateLeakStatePayoff .listener (lateLeakAnswered history.1.state (some (.reply answer)))

theorem lateLeakListenerDecision_expectedReward (late : Bool)
    (site : (lateLeakModel late).InformationSite .listener) (signal : LateLeakSignal)
    (at_signal : site.1 = .asked signal)
    (base : (lateLeakModel late).BehavioralPolicy .listener)
    (A : (lateLeakModel late).BehavioralAssessment)
    (choice : (lateLeakModel late).Choice .listener site.1) (answer : LateLeakAnswer)
    (same : choice.1 = some (.reply answer)) :
    (lateLeakListenerDecision late site signal at_signal base).expectedReward A choice =
      lateLeakAnswerReward A site answer := by
  simp only [InformationModel.ContinuationDecision.expectedReward,
    InformationModel.ContinuationDecision.posterior, expect_map, lateLeakAnswerReward]
  congr 1
  funext history
  simp only [Function.comp_apply, lateLeakListenerDecision, same]

/-- A supported answer is at least as good as every other answer. -/
theorem lateLeak_listener_support_maximal {A : (lateLeakModel late).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates late) (lateLeakPayoff late))
    (site : (lateLeakModel late).InformationSite .listener) (signal : LateLeakSignal)
    (at_signal : site.1 = .asked signal) (answer other : LateLeakAnswer)
    (fitsAnswer : answer.fits signal) (fitsOther : other.fits signal)
    (supported : lateLeakReplyLaw A.strategy signal (some (.reply answer)) ≠ 0) :
    lateLeakAnswerReward A site other ≤ lateLeakAnswerReward A site answer := by
  rcases site with ⟨info, decision⟩
  change info = .asked signal at at_signal
  subst at_signal
  let problem := lateLeakListenerDecision late ⟨.asked signal, decision⟩ signal rfl
    (A.strategy .listener)
  have maximal := problem.rational_support_maximal A
    ((A.isSequentiallyRational_iff_with _ _).mp rational)
    ⟨some (.reply answer), ⟨answer, rfl, fitsAnswer⟩⟩ (by
      rw [lateLeakReplyLaw_apply _ _ _ fitsAnswer] at supported
      exact (PMF.mem_support_iff _ _).mpr supported)
    ⟨some (.reply other), ⟨other, rfl, fitsOther⟩⟩
  simp only [InformationModel.ContinuationDecision.expectedReward,
    InformationModel.ContinuationDecision.posterior, expect_map] at maximal
  exact maximal

/-- An answer paying the same at every compatible state has that reward. -/
theorem lateLeak_answerReward_const (A : (lateLeakModel late).BehavioralAssessment)
    (site : (lateLeakModel late).InformationSite .listener) (signal : LateLeakSignal)
    (at_signal : site.1 = .asked signal) (answer : LateLeakAnswer) (value : ℝ)
    (each : ∀ secret resolution, lateLeakSignal secret resolution = signal →
      lateLeakListenerPayoff secret resolution answer = value) :
    lateLeakAnswerReward A site answer = value := by
  rw [lateLeakAnswerReward, ← expect_constant (A.belief .listener site) value]
  apply expect_congr_on_support
  intro history _
  obtain ⟨secret, resolution, state_eq, signal_eq⟩ :=
    lateLeak_listener_fiber_state (late := late) (signal := signal)
      ⟨history.1, history.2.trans at_signal⟩
  rw [state_eq]
  exact each secret resolution signal_eq

theorem lateLeakReplyLaw_bitZero (profile : LateLeakProfile late) (signal : LateLeakSignal)
    (failed : signal.success = false) :
    (lateLeakReplyLaw profile signal (some (.reply (.failure false)))).toReal =
      1 - lateLeakBitOneProb profile signal := by
  classical
  have computed := lateLeak_expect_two_point (lateLeakReplyLaw profile signal)
    (some (.reply (.failure true)))
    (fun choice => if some (LateLeakMove.reply (.failure false)) = choice then 1 else 0)
    1 (fun choice supported different => by
      obtain ⟨answer, rfl, fits⟩ := lateLeakReplyLaw_support profile signal choice supported
      cases answer with
      | failure bit =>
          cases bit
          · simp
          · exact (different rfl).elim
      | _ => simp_all [LateLeakAnswer.fits])
  rw [expect_ite_eq] at computed
  simpa [lateLeakBitOneProb] using computed

/-- After a failed opening it saw pending, the listener guesses the bit it
saw. -/
theorem lateLeak_rational_leaked_failure {A : (lateLeakModel late).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates late) (lateLeakPayoff late))
    (site : (lateLeakModel late).InformationSite .listener) (bit : Bool)
    (at_signal : site.1 = .asked (.leakedFailure bit)) :
    lateLeakBitOneProb A.strategy (.leakedFailure bit) = if bit then 1 else 0 := by
  have reward (guess : Bool) : lateLeakAnswerReward A site (.failure guess) =
      if guess = bit then 1 else 0 := by
    apply lateLeak_answerReward_const A site _ at_signal
    intro secret resolution signal_eq
    cases resolution <;> simp_all [lateLeakSignal, lateLeakListenerPayoff,
      LateLeakResolution.succeeded]
  have wrong : lateLeakReplyLaw A.strategy (.leakedFailure bit)
      (some (.reply (.failure (!bit)))) = 0 := by
    by_contra supported
    have maximal := lateLeak_listener_support_maximal rational site _ at_signal
      (.failure (!bit)) (.failure bit) (by cases bit <;> rfl) (by cases bit <;> rfl) supported
    rw [reward, reward] at maximal
    cases bit <;> norm_num at maximal
  cases bit
  · simpa [lateLeakBitOneProb] using congrArg ENNReal.toReal wrong
  · have zero := lateLeakReplyLaw_bitZero A.strategy (.leakedFailure true) rfl
    rw [show (!true) = false from rfl] at wrong
    rw [wrong, ENNReal.toReal_zero] at zero
    simp only [ite_true]
    linarith

theorem lateLeak_succeeded_of_signal {secret : LateLeakType} {resolution : LateLeakResolution}
    {signal : LateLeakSignal} (same : lateLeakSignal secret resolution = signal)
    (success : signal.success = true) : resolution.succeeded = true := by
  subst same
  cases resolution <;> simp_all [lateLeakSignal, LateLeakSignal.success,
    LateLeakResolution.succeeded]

/-- A success signal and the label determine the type and resolution. -/
theorem lateLeak_success_signal_label {secret other : LateLeakType}
    {resolution otherResolution : LateLeakResolution} {signal : LateLeakSignal}
    (success : signal.success = true) (first : lateLeakSignal secret resolution = signal)
    (second : lateLeakSignal other otherResolution = signal) (label : secret.2 = other.2) :
    secret = other ∧ resolution = otherResolution := by
  subst first
  cases resolution <;> cases otherResolution <;>
    simp_all [lateLeakSignal, LateLeakSignal.success, Prod.ext_iff]

/-- The reward of guessing a label is the belief of the only compatible history
with that label. -/
theorem lateLeak_guess_reward_eq (A : (lateLeakModel late).BehavioralAssessment)
    (site : (lateLeakModel late).InformationSite .listener) (signal : LateLeakSignal)
    (at_signal : site.1 = .asked signal) (success : signal.success = true)
    (history : (lateLeakModel late).InformationHistory .listener site.1)
    (secret : LateLeakType) (resolution : LateLeakResolution)
    (state_eq : history.1.state = .answering secret resolution) :
    lateLeakAnswerReward A site (.guess secret.2) = (A.belief .listener site history).toReal := by
  classical
  obtain ⟨_, _, own_state, own_signal⟩ :=
    lateLeak_listener_fiber_state (late := late) (signal := signal)
      ⟨history.1, history.2.trans at_signal⟩
  rw [state_eq] at own_state
  cases own_state
  rw [lateLeakAnswerReward, ← mul_one (A.belief .listener site history).toReal, ← expect_ite_eq]
  apply expect_congr_on_support
  intro other _
  obtain ⟨otherSecret, otherResolution, other_state, other_signal⟩ :=
    lateLeak_listener_fiber_state (late := late) (signal := signal)
      ⟨other.1, other.2.trans at_signal⟩
  have succeeded : otherResolution.succeeded = true :=
    lateLeak_succeeded_of_signal other_signal success
  change lateLeakStatePayoff .listener (lateLeakAnswered other.1.state _) = _
  rw [other_state]
  simp only [lateLeakAnswered, lateLeakReplyOf, lateLeakStatePayoff, lateLeakListenerPayoff,
    succeeded, ite_true]
  by_cases same : secret.2 = otherSecret.2
  · obtain ⟨rfl, rfl⟩ := lateLeak_success_signal_label success own_signal other_signal same
    have equal : history = other := Subtype.ext (lateLeak_history_eq_of_state_eq
      (state_eq.trans other_state.symm))
    simp [equal]
  · have different : history ≠ other := by
      intro equal
      rw [← equal, state_eq] at other_state
      cases other_state
      exact same rfl
    simp [same, different]

/-- The reward of guessing a label vanishes when the belief leaves out the only
compatible history with that label. -/
theorem lateLeak_guess_reward_zero (A : (lateLeakModel late).BehavioralAssessment)
    (site : (lateLeakModel late).InformationSite .listener) (signal : LateLeakSignal)
    (at_signal : site.1 = .asked signal) (success : signal.success = true)
    (history : (lateLeakModel late).InformationHistory .listener site.1)
    (secret : LateLeakType) (resolution : LateLeakResolution)
    (state_eq : history.1.state = .answering secret resolution)
    (zero : A.belief .listener site history = 0) :
    lateLeakAnswerReward A site (.guess secret.2) = 0 := by
  rw [lateLeak_guess_reward_eq A site signal at_signal success history secret resolution state_eq,
    zero, ENNReal.toReal_zero]

/-- The safe answer is worth `2/5` after every success. -/
theorem lateLeak_safe_reward (A : (lateLeakModel late).BehavioralAssessment)
    (site : (lateLeakModel late).InformationSite .listener) (signal : LateLeakSignal)
    (at_signal : site.1 = .asked signal) (success : signal.success = true) :
    lateLeakAnswerReward A site .safe = 2 / 5 := by
  apply lateLeak_answerReward_const A site _ at_signal
  intro secret resolution signal_eq
  simp [lateLeakListenerPayoff, lateLeak_succeeded_of_signal signal_eq success]

/-- After a success the three label guesses are worth one in total. -/
theorem lateLeak_guess_rewards_total (A : (lateLeakModel late).BehavioralAssessment)
    (site : (lateLeakModel late).InformationSite .listener) (signal : LateLeakSignal)
    (at_signal : site.1 = .asked signal) (success : signal.success = true) :
    lateLeakAnswerReward A site (.guess .a) + lateLeakAnswerReward A site (.guess .b) +
      lateLeakAnswerReward A site (.guess .c) = 1 := by
  simp only [lateLeakAnswerReward]
  rw [← expect_add_of_finite, ← expect_add_of_finite,
    ← expect_constant (A.belief .listener site) 1]
  apply expect_congr_on_support
  intro history _
  obtain ⟨secret, resolution, state_eq, signal_eq⟩ :=
    lateLeak_listener_fiber_state (late := late) (signal := signal)
      ⟨history.1, history.2.trans at_signal⟩
  have succeeded : resolution.succeeded = true :=
    lateLeak_succeeded_of_signal signal_eq success
  change lateLeakStatePayoff .listener (lateLeakAnswered history.1.state _) +
    lateLeakStatePayoff .listener (lateLeakAnswered history.1.state _) +
    lateLeakStatePayoff .listener (lateLeakAnswered history.1.state _) = 1
  rw [state_eq]
  rcases secret with ⟨bit, own⟩
  cases own <;> simp [lateLeakAnswered, lateLeakReplyOf, lateLeakStatePayoff,
    lateLeakListenerPayoff, succeeded]

theorem lateLeak_safe_fits {signal : LateLeakSignal} (success : signal.success = true) :
    LateLeakAnswer.safe.fits signal := by
  simpa [LateLeakAnswer.fits] using success

theorem lateLeak_guess_fits {signal : LateLeakSignal} (success : signal.success = true)
    (label : LateLeakLabel) : (LateLeakAnswer.guess label).fits signal := by
  simpa [LateLeakAnswer.fits] using success

/-- After a success, a belief leaving out one label makes the listener guess. -/
theorem lateLeak_rational_guesses {A : (lateLeakModel late).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates late) (lateLeakPayoff late))
    (site : (lateLeakModel late).InformationSite .listener) (signal : LateLeakSignal)
    (at_signal : site.1 = .asked signal) (success : signal.success = true)
    (label : LateLeakLabel) (unlikely : lateLeakAnswerReward A site (.guess label) = 0) :
    lateLeakSafeProb A.strategy signal = 0 := by
  by_contra positive
  have supported : lateLeakReplyLaw A.strategy signal (some (.reply .safe)) ≠ 0 := by
    intro zero
    exact positive (by rw [lateLeakSafeProb, zero, ENNReal.toReal_zero])
  have bound (other : LateLeakLabel) : lateLeakAnswerReward A site (.guess other) ≤ 2 / 5 :=
    lateLeak_safe_reward A site signal at_signal success ▸
      lateLeak_listener_support_maximal rational site signal at_signal .safe (.guess other)
        (lateLeak_safe_fits success) (lateLeak_guess_fits success other) supported
  have total := lateLeak_guess_rewards_total A site signal at_signal success
  have ba := bound .a
  have bb := bound .b
  have bc := bound .c
  cases label <;> rw [unlikely] at total <;> linarith

end Vegas
