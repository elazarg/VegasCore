/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Intended
import GameTheory.Analysis.Protocol.SequentialExistence
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Preservation under sufficiently large failure costs

Late attempts have a fixed positive probability of failure. A sufficiently
large failure forfeit and drop charge make every deferred continuation worse
than every protected success, irrespective of the listener's replies.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter

variable {G : LateLeakParameters} {late : Bool}

theorem lateLeak_sender_success_nonnegative (reward : 0 ≤ G.reward)
    (profile : LateLeakProfile G late) (secret : LateLeakType)
    (resolution : LateLeakResolution) (success : resolution.succeeded = true) :
    0 ≤ lateLeakAnswerValue profile (lateLeakStatePayoff G .sender) secret resolution := by
  rw [lateLeak_sender_success_value profile secret resolution success]
  have m0 := lateLeakSafeProb_nonneg profile (lateLeakSignal secret resolution)
  have m1 := lateLeakSafeProb_le_one profile (lateLeakSignal secret resolution)
  have g0 : 0 ≤ lateLeakGuessGain G secret.2 := by
    cases secret.2 <;> simp [lateLeakGuessGain, reward]
  exact add_nonneg (mul_nonneg m0 (by linarith))
    (mul_nonneg (sub_nonneg.mpr m1) g0)

theorem lateLeak_sender_success_le_reward (reward : 0 ≤ G.reward)
    (profile : LateLeakProfile G late) (secret : LateLeakType)
    (resolution : LateLeakResolution) (success : resolution.succeeded = true) :
    lateLeakAnswerValue profile (lateLeakStatePayoff G .sender) secret resolution ≤ G.reward := by
  rw [lateLeak_sender_success_value profile secret resolution success]
  have m0 := lateLeakSafeProb_nonneg profile (lateLeakSignal secret resolution)
  have m1 := lateLeakSafeProb_le_one profile (lateLeakSignal secret resolution)
  have gr : lateLeakGuessGain G secret.2 ≤ G.reward := by
    cases secret.2 <;> simp [lateLeakGuessGain, reward]
  have bound := mul_le_mul_of_nonneg_left gr (sub_nonneg.mpr m1)
  nlinarith [mul_nonneg m0 reward]

theorem lateLeak_sender_failure_le_reward (reward : 0 ≤ G.reward)
    (profile : LateLeakProfile G late) (secret : LateLeakType)
    (resolution : LateLeakResolution) (failure : resolution.succeeded = false) :
    lateLeakAnswerValue profile (lateLeakStatePayoff G .sender) secret resolution ≤
      G.reward - G.forfeit - (if resolution.droppedLate then G.dropCharge else 0) := by
  rw [lateLeak_sender_failure_value profile secret resolution failure]
  have b0 := lateLeakBitOneProb_nonneg profile (lateLeakSignal secret resolution)
  have b1 := lateLeakBitOneProb_le_one profile (lateLeakSignal secret resolution)
  have oneBound : lateLeakBitOneGain G secret.2 ≤ G.reward := by
    cases secret.2 <;> simp [lateLeakBitOneGain, reward]
  have zeroBound : lateLeakBitZeroGain G secret.2 ≤ G.reward := by
    cases secret.2 <;> simp [lateLeakBitZeroGain, reward]
  nlinarith [mul_le_mul_of_nonneg_left oneBound b0,
    mul_le_mul_of_nonneg_left zeroBound (sub_nonneg.mpr b1)]

theorem lateLeak_sender_late_send_le (reward : 0 ≤ G.reward)
    (profile : LateLeakProfile G late) (secret : LateLeakType)
    (included dropped : LateLeakResolution)
    (success : included.succeeded = true) (failure : dropped.succeeded = false)
    (charged : dropped.droppedLate = true) :
    lateLeakSendValue profile (lateLeakStatePayoff G .sender) secret included dropped ≤
      G.reward - (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge) := by
  have upperSuccess := lateLeak_sender_success_le_reward reward profile secret included success
  have upperFailure := lateLeak_sender_failure_le_reward reward profile secret dropped failure
  rw [charged] at upperFailure
  simp only [ite_true] at upperFailure
  have q0 := (lateLeakInclusionProb_pos G).le
  have q1 := (lateLeakInclusionProb_lt_one G).le
  unfold lateLeakSendValue
  nlinarith [mul_le_mul_of_nonneg_left upperSuccess q0,
    mul_le_mul_of_nonneg_left upperFailure (sub_nonneg.mpr q1)]

private theorem convex_lt {p a b upper : ℝ} (p0 : 0 ≤ p) (p1 : p ≤ 1)
    (aUpper : a < upper) (bUpper : b < upper) : p * a + (1 - p) * b < upper := by
  have bound : p * a + (1 - p) * b ≤ max a b := by
    nlinarith [mul_le_mul_of_nonneg_left (le_max_left a b) p0,
      mul_le_mul_of_nonneg_left (le_max_right a b) (sub_nonneg.mpr p1)]
  exact bound.trans_lt (max_lt aUpper bUpper)

theorem lateLeak_sender_deferral_lt {bound : ℝ} (reward : 0 ≤ G.reward)
    (never : G.reward - G.forfeit < bound)
    (attempt : G.reward - (1 - lateLeakInclusionProb G) *
      (G.forfeit + G.dropCharge) < bound)
    (profile : LateLeakProfile G late) (secret : LateLeakType) :
    lateLeakFirstValue profile (lateLeakStatePayoff G .sender) secret < bound := by
  have first := lateLeak_sender_late_send_le reward profile secret
    .firstIncluded .firstDropped rfl rfl rfl
  have second := lateLeak_sender_late_send_le reward profile secret
    .secondIncluded .secondDropped rfl rfl rfl
  have withheld := lateLeak_sender_failure_le_reward reward profile secret .withheld rfl
  simp only [LateLeakResolution.droppedLate, Bool.false_eq_true, ite_false, sub_zero] at withheld
  have p0 := lateLeakOpenProb_nonneg profile (.secondLate secret)
  have p1 := lateLeakOpenProb_le_one profile (.secondLate secret)
  have secondBound : lateLeakSecondValue profile (lateLeakStatePayoff G .sender) secret <
      bound := by
    unfold lateLeakSecondValue
    have a := second.trans_lt attempt
    have b := withheld.trans_lt never
    exact convex_lt p0 p1 a b
  have f0 := lateLeakOpenProb_nonneg profile (.firstLate secret)
  have f1 := lateLeakOpenProb_le_one profile (.firstLate secret)
  unfold lateLeakFirstValue
  have firstBound := first.trans_lt attempt
  exact convex_lt f0 f1 firstBound secondBound

private theorem listener_ownPlay_empty :
    ∀ {state : LateLeakState} (trace : (lateLeakExecution G late).Trace state),
      ¬ state.IsFinished → (lateLeakModel G late).ownPlay .listener trace = []
  | _, .start, _ => rfl
  | _, .extend (source := source) (target := target) prior joint legal realized, running => by
      have inactive : source.actor ≠ some .listener := by
        change target ∈ (lateLeakAdvance G source (joint source.mover)).support at realized
        cases source with
        | answering secret resolution =>
            simp only [lateLeakAdvance, PMF.mem_support_pure_iff] at realized
            subst realized
            exact (running trivial).elim
        | _ => simp [LateLeakState.actor]
      have silent := LegalOption.eq_none_of_inactive (E := lateLeakExecution G late)
        (joint .listener) ((lateLeakExecution G late).legalOption_of_legal legal .listener) inactive
      rw [InfoSignals.ownPlay_extend, silent]
      exact listener_ownPlay_empty prior legal.1

/-- The sender knows its full history; the listener acts only once. -/
theorem lateLeak_decisionRecall (G : LateLeakParameters) (late : Bool) :
    (lateLeakModel G late).DecisionRecall := by
  intro who site first second
  cases who with
  | sender =>
      have views := (lateLeak_fiber_view first).trans (lateLeak_fiber_view second).symm
      have same := lateLeak_history_eq_of_state_eq (LateLeakView.full.inj views)
      exact congrArg (fun history => (lateLeakModel G late).ownPlay .sender history.trace) same
  | listener =>
      rw [listener_ownPlay_empty first.1.trace (lateLeak_fiber_not_finished site first),
        listener_ownPlay_empty second.1.trace (lateLeak_fiber_not_finished site second)]

/-- If every deferred continuation is negative, rational senders open protected. -/
theorem lateLeak_rational_protected_opens (reward : 0 ≤ G.reward)
    (never : G.reward < G.forfeit)
    (attempt : G.reward < (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))
    {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (secret : LateLeakType) : lateLeakOpenProb A.strategy (.protectedTurn secret) = 1 := by
  let deviation := lateLeakCommitOpen (A.strategy .sender) (.protectedTurn secret) true
    (lateLeak_sender_open_allowed true (.protectedTurn secret) rfl)
  have optimal := lateLeak_sender_rational rational
    (lateLeakSenderSite G true (lateLeakTypeHistory G true secret) rfl)
    (state := .protectedTurn secret) rfl deviation
  rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn,
    lateLeakValue_protectedTurn, lateLeakProtectedValue, lateLeakProtectedValue,
    lateLeakOpenProb_update_commit_self] at optimal
  simp only [ite_true, one_mul, sub_self, zero_mul, add_zero,
    lateLeakAnswerValue_update_sender] at optimal
  have positive := lateLeak_sender_success_nonnegative reward A.strategy secret .protectedOpen rfl
  have negative := lateLeak_sender_deferral_lt (bound := 0) reward (by linarith) (by linarith)
    A.strategy secret
  have p1 := lateLeakOpenProb_le_one A.strategy (.protectedTurn secret)
  have gap : 0 <
      lateLeakAnswerValue A.strategy (lateLeakStatePayoff G .sender) secret .protectedOpen -
      lateLeakFirstValue A.strategy (lateLeakStatePayoff G .sender) secret := by linarith
  have product : (1 - lateLeakOpenProb A.strategy (.protectedTurn secret)) *
      (lateLeakAnswerValue A.strategy (lateLeakStatePayoff G .sender) secret .protectedOpen -
        lateLeakFirstValue A.strategy (lateLeakStatePayoff G .sender) secret) ≤ 0 := by
    nlinarith [optimal]
  rcases lt_or_eq_of_le p1 with lower | equal
  · have strict := mul_pos (sub_pos.mpr lower) gap
    linarith
  · exact equal

private theorem opening_eq_pure (profile : LateLeakProfile G true) (secret : LateLeakType)
    (opens : lateLeakOpenProb profile (.protectedTurn secret) = 1) :
    lateLeakOpeningLaw profile (.protectedTurn secret) = PMF.pure (some (.opening true)) := by
  have one : lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening true)) = 1 := by
    rw [← ENNReal.toReal_eq_one_iff]
    exact opens
  exact pmf_eq_pure_of_support_subset_singleton _ _
    (le_of_eq ((PMF.apply_eq_one_iff _ _).mp one))

private def protectedMember (secret : LateLeakType) :
    (lateLeakModel G true).InformationHistory .listener (.asked (.protectedSuccess secret.1)) :=
  lateLeakListenerMember G true (lateLeakOpenedHistory G true secret)
    (.protectedSuccess secret.1) rfl

private theorem protected_guess_reward (A : (lateLeakModel G true).BehavioralAssessment)
    (bit : Bool)
    (decision : (lateLeakModel G true).IsDecisionInfo .listener (.asked (.protectedSuccess bit)))
    (uniform : ∀ label other : LateLeakLabel,
      A.belief .listener ⟨_, decision⟩ (protectedMember (G := G) (bit, label)) =
        A.belief .listener ⟨_, decision⟩ (protectedMember (G := G) (bit, other)))
    (label : LateLeakLabel) : lateLeakAnswerReward A ⟨_, decision⟩ (.guess label) = 1 / 3 := by
  have reward (other : LateLeakLabel) : lateLeakAnswerReward A ⟨_, decision⟩ (.guess other) =
      (A.belief .listener ⟨_, decision⟩ (protectedMember (G := G) (bit, .a))).toReal := by
    rw [← uniform other .a]
    exact lateLeak_guess_reward_eq A ⟨_, decision⟩ (.protectedSuccess bit) rfl rfl
      (protectedMember (G := G) (bit, other)) (bit, other) .protectedOpen rfl
  have total := lateLeak_guess_rewards_total A ⟨_, decision⟩ (.protectedSuccess bit) rfl rfl
  rw [reward, reward, reward] at total
  rw [reward]
  linarith

/-- Rationality and Bayes' rule on the protected path suffice to force the safe reply. -/
theorem lateLeak_rational_bayes_protected_safe {A : (lateLeakModel G true).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G true) (lateLeakPayoff G true))
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (lateLeakModel G true) A (lateLeak_antichain G true))
    (opens : ∀ secret, lateLeakOpenProb A.strategy (.protectedTurn secret) = 1)
    (bit : Bool) : lateLeakReplyLaw A.strategy (.protectedSuccess bit) =
      PMF.pure (some (.reply .safe)) := by
  let site := lateLeakListenerSite G true (lateLeakOpenedHistory G true (bit, .a))
    (.protectedSuccess bit) rfl .safe rfl
  have weight (secret : LateLeakType) : (lateLeakModel G true).historyReachWeight A.strategy
      (lateLeakOpenedHistory G true secret) = lateLeakPrior secret := by
    rw [lateLeak_weight_opened, opening_eq_pure A.strategy secret (opens secret),
      PMF.pure_apply_self, mul_one]
  have mass : 0 < (lateLeakModel G true).informationMass A.strategy .listener site := by
    apply ((lateLeakModel G true).informationMass_pos_iff _ _ _).mpr
    refine ⟨protectedMember (G := G) (bit, .a), ?_⟩
    change 0 < (lateLeakModel G true).historyReachWeight A.strategy
      (lateLeakOpenedHistory G true (bit, .a))
    rw [weight]
    exact pos_iff_ne_zero.mpr (lateLeakPrior_ne_zero _)
  have uniform (label other : LateLeakLabel) :
      A.belief .listener site (protectedMember (G := G) (bit, label)) =
        A.belief .listener site (protectedMember (G := G) (bit, other)) := by
    calc
      _ = (lateLeakModel G true).historyReachWeight A.strategy
          (lateLeakOpenedHistory G true (bit, label)) /
          (lateLeakModel G true).informationMass A.strategy .listener site :=
        bayes .listener site mass (protectedMember (G := G) (bit, label))
      _ = (lateLeakModel G true).historyReachWeight A.strategy
          (lateLeakOpenedHistory G true (bit, other)) /
          (lateLeakModel G true).informationMass A.strategy .listener site := by
        rw [weight, weight]
        rfl
      _ = _ := (bayes .listener site mass (protectedMember (G := G) (bit, other))).symm
  apply pmf_eq_pure_of_support_subset_singleton
  intro choice supported
  obtain ⟨answer, rfl, fits⟩ := lateLeakReplyLaw_support A.strategy _ choice supported
  cases answer with
  | safe => rfl
  | guess label =>
      have maximal := lateLeak_listener_support_maximal rational site _ rfl
        (.guess label) .safe fits rfl ((PMF.mem_support_iff _ _).mp supported)
      have guess := protected_guess_reward A bit site.2 uniform label
      change lateLeakAnswerReward A site (.guess label) = 1 / 3 at guess
      rw [lateLeak_safe_reward A site _ rfl rfl, guess] at maximal
      norm_num at maximal
  | failure bit => simp [LateLeakAnswer.fits, LateLeakSignal.success] at fits

theorem lateLeak_rational_protected_safe {A : (lateLeakModel G true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true))
    (opens : ∀ secret, lateLeakOpenProb A.strategy (.protectedTurn secret) = 1)
    (bit : Bool) : lateLeakReplyLaw A.strategy (.protectedSuccess bit) =
      PMF.pure (some (.reply .safe)) :=
  lateLeak_rational_bayes_protected_safe equilibrium.1
    (equilibrium.2.isBayesConsistent (lateLeak_antichain G true)) opens bit

theorem lateLeak_intended_law_of_protected (profile : LateLeakProfile G true)
    (opens : ∀ secret, lateLeakOpenProb profile (.protectedTurn secret) = 1)
    (safe : ∀ bit, lateLeakReplyLaw profile (.protectedSuccess bit) =
      PMF.pure (some (.reply .safe))) :
    lateLeakOutcomeLaw G true profile = lateLeakIntendedOutcome := by
  rw [lateLeakOutcomeLaw_eq, Function.iterate_succ_apply, lateLeakFlow_pure,
    lateLeakFlow_iterate_eq_bind]
  change ((lateLeakMoveLaw profile .initial).bind
    fun _ => lateLeakPrior.map LateLeakState.protectedTurn).bind _ = _
  rw [PMF.bind_const, PMF.bind_map, lateLeakIntendedOutcome, ← PMF.bind_pure_comp]
  congr 1
  funext secret
  simp only [Function.comp_apply]
  rw [Function.iterate_succ_apply, lateLeakFlow_pure]
  change (lateLeakFlow profile)^[3] ((lateLeakOpeningLaw profile (.protectedTurn secret)).bind
    (lateLeakAdvance G (.protectedTurn secret))) = _
  rw [opening_eq_pure profile secret (opens secret), PMF.pure_bind]
  simp only [lateLeakAdvance, ite_true]
  rw [Function.iterate_succ_apply, lateLeakFlow_pure]
  change (lateLeakFlow profile)^[2]
    ((lateLeakReplyLaw profile (lateLeakSignal secret .protectedOpen)).bind
      (lateLeakAdvance G (.answering secret .protectedOpen))) = _
  rw [lateLeakSignal, safe, PMF.pure_bind]
  simp only [lateLeakAdvance, lateLeakReplyOf]
  have fixed (fuel : ℕ) :
      (lateLeakFlow profile)^[fuel] (PMF.pure (.finished secret .protectedOpen .safe)) =
      PMF.pure (.finished secret .protectedOpen .safe) := by
    induction fuel with
    | zero => rfl
    | succ fuel ih =>
        rw [Function.iterate_succ_apply, lateLeakFlow_pure, lateLeakKernel_finished, ih]
  exact fixed 2

/-- Strong conditional failure costs force the intended outcome in every
sequential equilibrium, even when pending late openings disclose their value. -/
theorem lateLeak_outcome_preserved_of_failure_costs (reward : 0 ≤ G.reward)
    (never : G.reward < G.forfeit)
    (attempt : G.reward < (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))
    (A : (lateLeakModel G true).BehavioralAssessment)
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome := by
  have opens := lateLeak_rational_protected_opens reward never attempt equilibrium.1
  exact lateLeak_intended_law_of_protected A.strategy opens
    (lateLeak_rational_protected_safe equilibrium opens)

/-- The finite late-turn game has a preserving sequential equilibrium when
failure costs exceed the worst possible gain from any deferred continuation. -/
theorem lateLeak_preserving_equilibrium_of_failure_costs (reward : 0 ≤ G.reward)
    (never : G.reward < G.forfeit)
    (attempt : G.reward < (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge)) :
    ∃ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true)
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome := by
  let fallback : ∀ who, (lateLeakModel G true).Policy who :=
    fun _ _ => Classical.choice inferInstance
  obtain ⟨A, rational, consistent⟩ := (lateLeakModel G true).exists_sequentialEquilibrium
    (lateLeak_decisionRecall G true) fallback (lateLeakPayoff G true) (lateLeak_terminates G true)
  have equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G true)
      (lateLeak_terminates G true) (lateLeakPayoff G true) := ⟨rational, consistent⟩
  exact ⟨A, equilibrium,
    lateLeak_outcome_preserved_of_failure_costs reward never attempt A equilibrium⟩

/-- A finite drop charge suffices at each fixed inclusion probability below one. -/
theorem lateLeak_preserving_equilibrium_of_dropCharge_bound (reward : 0 ≤ G.reward)
    (never : G.reward < G.forfeit)
    (charge : G.reward / (1 - lateLeakInclusionProb G) ≤ G.dropCharge) :
    ∃ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true)
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome := by
  have delta : 0 < 1 - lateLeakInclusionProb G := sub_pos.mpr (lateLeakInclusionProb_lt_one G)
  have collected : G.reward ≤ (1 - lateLeakInclusionProb G) * G.dropCharge := by
    have bound := (div_le_iff₀ delta).mp charge
    nlinarith [bound]
  apply lateLeak_preserving_equilibrium_of_failure_costs reward never
  have positive : 0 < G.forfeit := lt_of_le_of_lt reward never
  nlinarith [mul_pos delta positive]

/-- For any fixed inclusion probability below one and forfeit above the
reward range, some nonnegative finite drop charge restores SE preservation. -/
theorem lateLeak_exists_preserving_dropCharge (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (never : G.reward < G.forfeit) :
    ∃ charge : ℝ, 0 ≤ charge ∧
      ∃ A : (lateLeakModel { G with dropCharge := charge } true).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain { G with dropCharge := charge } true)
          (lateLeak_terminates { G with dropCharge := charge } true)
          (lateLeakPayoff { G with dropCharge := charge } true) ∧
        lateLeakOutcomeLaw { G with dropCharge := charge } true A.strategy =
          lateLeakIntendedOutcome := by
  refine ⟨G.reward / (1 - lateLeakInclusionProb G), div_nonneg reward
    (sub_pos.mpr (lateLeakInclusionProb_lt_one G)).le, ?_⟩
  exact lateLeak_preserving_equilibrium_of_dropCharge_bound reward never (le_refl _)

end Vegas
