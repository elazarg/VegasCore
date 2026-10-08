/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.CompleteObservationValue
import Vegas.Examples.LateLeak.CompleteObservationPosterior
import GameTheoryExtensions.Analysis.Protocol.ContinuationDecision
import GameTheoryExtensions.Math.Probability.Support

/-! # Sequential equilibrium under complete opening observation

The listener has one final native decision. The sender's bound compares whole
adaptive policies; the listener's reduction compares arbitrary response laws at
the refined information containing the complete public opening transcript.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : LateLeakParameters}

/-- Every native listener response terminates the opening phase immediately. -/
theorem lateOpeningPublicKernel_answering (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (secret : LateLeakType)
    (resolution : LateLeakResolution)
    (trace : (lateLeakExecution G true).Trace (.answering secret resolution)) :
    lateOpeningPublicKernel G profile (.answering secret resolution) =
      (profile .listener ((lateOpeningPublicModel G).infoOf .listener trace)).map
        (fun choice => .finished secret resolution (lateLeakReplyOf choice.1)) := by
  rw [lateOpeningPublicKernel_move_law G profile ⟨_, trace⟩
    (by simp [LateLeakState.IsFinished]), PMF.bind_map]
  rfl

/-- The terminal expected payoff is the current listener response's reward.
Later policy values cannot affect the law because every response terminates. -/
theorem lateOpeningPublic_answering_continuation_value (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (who : LateLeakRole) (secret : LateLeakType)
    (resolution : LateLeakResolution)
    (trace : (lateLeakExecution G true).Trace (.answering secret resolution)) :
    expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom
      (lateLeak_terminates G true) profile ⟨_, trace⟩) (lateLeakPayoff G true who) =
      expect (profile .listener ((lateOpeningPublicModel G).infoOf .listener trace))
        (fun choice => lateLeakStatePayoff G who
          (.finished secret resolution (lateLeakReplyOf choice.1))) := by
  classical
  let kernel := lateOpeningPublicKernel G profile
  let law := kernel (.answering secret resolution)
  have fixed : law.bind kernel = law := by
    dsimp only [law, kernel]
    rw [lateOpeningPublicKernel_answering G profile secret resolution trace, PMF.bind_map]
    change (profile .listener ((lateOpeningPublicModel G).infoOf .listener trace)).bind
      (fun choice => lateOpeningPublicKernel G profile
        (.finished secret resolution (lateLeakReplyOf choice.1))) = _
    simp only [lateOpeningPublicKernel_terminal G profile
      (.finished secret resolution _) (by trivial)]
    rfl
  have iterate (fuel : ℕ) :
      (fun next => next.bind kernel)^[fuel] law = law := by
    induction fuel with
    | zero => rfl
    | succ fuel ih => rw [Function.iterate_succ_apply', ih, fixed]
  rw [show lateLeakPayoff G true who =
    (lateLeakStatePayoff G who) ∘ ExecutionProtocol.History.state from rfl,
    ← expect_map, lateOpeningPublic_terminal_map_state,
    show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply, PMF.pure_bind]
  change expect ((fun next => next.bind kernel)^[4] law) _ = _
  rw [iterate]
  dsimp only [law, kernel]
  rw [lateOpeningPublicKernel_answering G profile secret resolution trace, expect_map]
  rfl

/-- A whole continuation decision over the actual refined information set. -/
def lateOpeningPublicListenerDecision (G : LateLeakParameters) (bit : Bool)
    (resolution : LateLeakResolution)
    (base : (lateOpeningPublicModel G).BehavioralPolicy .listener) :
    (lateOpeningPublicModel G).ContinuationDecision (lateLeakPayoff G true)
      ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true))
      LateLeakState
      ((lateOpeningPublicModel G).Choice .listener
        (lateOpeningPublicListenerInfo (G := G) bit resolution)) where
  player := .listener
  site := lateOpeningPublicListenerSite G bit resolution
  state history := history.1.state
  response profile := profile .listener (lateOpeningPublicListenerInfo bit resolution)
  response_finite _ := Set.toFinite _
  reward state choice := lateLeakStatePayoff G .listener (lateLeakAnswered state choice.1)
  policy choice := base.commit (lateOpeningPublicListenerInfo bit resolution) choice
  history_value profile history := by
    obtain ⟨secret, state, _known⟩ :=
      lateOpeningPublic_listener_fiber_state bit resolution history
    cases history with
    | mk history observed =>
      rcases history with ⟨actual, trace⟩
      change actual = _ at state
      subst actual
      rw [lateOpeningPublic_answering_continuation_value G profile .listener
          secret resolution trace,
        observed]
      rfl
  realize profile choice := by
    simp only [Profile.update_same, InformationModel.BehavioralPolicy.commit_self]

/-- Expected reward of one ordinary reply under the actual listener belief. -/
def lateOpeningPublicAnswerReward
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment) (bit : Bool)
    (resolution : LateLeakResolution) (answer : LateLeakAnswer) : ℝ :=
  expect (assessment.belief .listener (lateOpeningPublicListenerSite G bit resolution))
    (fun history => lateLeakStatePayoff G .listener
      (lateLeakAnswered history.1.state (some (.reply answer))))

theorem lateOpeningPublicListenerDecision_expectedReward
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment) (bit : Bool)
    (resolution : LateLeakResolution) (base : (lateOpeningPublicModel G).BehavioralPolicy .listener)
    (choice : (lateOpeningPublicModel G).Choice .listener
      (lateOpeningPublicListenerInfo (G := G) bit resolution))
    (answer : LateLeakAnswer) (same : choice.1 = some (.reply answer)) :
    (lateOpeningPublicListenerDecision G bit resolution base).expectedReward assessment choice =
      lateOpeningPublicAnswerReward assessment bit resolution answer := by
  simp only [InformationModel.ContinuationDecision.expectedReward,
    InformationModel.ContinuationDecision.posterior, expect_map, lateOpeningPublicAnswerReward]
  congr 1
  funext history
  simp only [Function.comp_apply, lateOpeningPublicListenerDecision, same]

/-- Known emitted bits make the truthful failure response uniquely optimal. -/
theorem lateOpeningPublic_failed_emission_reward
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment) (bit : Bool)
    (resolution : LateLeakResolution) (emitted : resolution ≠ .withheld)
    (failed : resolution.succeeded = false) (guess : Bool) :
    lateOpeningPublicAnswerReward assessment bit resolution (.failure guess) =
      if guess = bit then 1 else 0 := by
  rw [lateOpeningPublicAnswerReward, ← expect_constant _ (if guess = bit then 1 else 0)]
  apply expect_congr_on_support
  intro history _
  obtain ⟨secret, state, known⟩ :=
    lateOpeningPublic_listener_fiber_state bit resolution history
  rw [state]
  simp [lateLeakStatePayoff, lateLeakAnswered, lateLeakReplyOf,
    lateLeakListenerPayoff, failed, known emitted]

/-- Every label guess has its exact posterior atom as its reward. -/
theorem lateOpeningPublic_success_guess_reward
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment) (bit : Bool)
    (resolution : LateLeakResolution) (emitted : resolution ≠ .withheld)
    (success : resolution.succeeded = true) (label : LateLeakLabel) :
    lateOpeningPublicAnswerReward assessment bit resolution (.guess label) =
      (assessment.belief .listener (lateOpeningPublicListenerSite G bit resolution)
        (lateOpeningPublicAnswerMember G bit resolution label)).toReal := by
  classical
  rw [lateOpeningPublicAnswerReward]
  rw [← mul_one (assessment.belief .listener (lateOpeningPublicListenerSite G bit resolution)
    (lateOpeningPublicAnswerMember G bit resolution label)).toReal, ← expect_ite_eq]
  apply expect_congr_on_support
  intro history _
  obtain ⟨other, rfl⟩ := lateOpeningPublic_emitted_fiber_members bit resolution emitted history
  have equal : (lateOpeningPublicAnswerMember G bit resolution label =
      lateOpeningPublicAnswerMember G bit resolution other) ↔ label = other :=
    (lateOpeningPublicEmittedFiberEquiv bit resolution emitted).injective.eq_iff
  have equal_history : (lateOpeningPublicAnswerHistory G (bit, label) resolution =
      lateOpeningPublicAnswerHistory G (bit, other) resolution) ↔ label = other := by
    simpa only [lateOpeningPublicAnswerMember, Subtype.mk.injEq] using equal
  simp [lateOpeningPublicAnswerMember, lateOpeningPublicAnswerHistory_state,
    lateLeakStatePayoff, lateLeakAnswered, lateLeakReplyOf, lateLeakListenerPayoff,
    success, equal_history]

/-- The safe reply has constant reward at every successful public resolution. -/
theorem lateOpeningPublic_success_safe_reward
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment) (bit : Bool)
    (resolution : LateLeakResolution) (success : resolution.succeeded = true) :
    lateOpeningPublicAnswerReward assessment bit resolution .safe = 2 / 5 := by
  rw [lateOpeningPublicAnswerReward, ← expect_constant _ (2 / 5)]
  apply expect_congr_on_support
  intro history _
  obtain ⟨secret, state, _known⟩ :=
    lateOpeningPublic_listener_fiber_state bit resolution history
  rw [state]
  simp [lateLeakStatePayoff, lateLeakAnswered, lateLeakReplyOf, lateLeakListenerPayoff, success]

/-- The withholding fiber has the original prior's two exact bit rewards. -/
theorem lateOpeningPublic_withheld_reward
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment)
    (prior : ∀ secret, assessment.belief .listener
      (lateOpeningPublicListenerSite G false .withheld)
      (lateOpeningPublicWithheldMember G secret) = lateLeakPrior secret) (guess : Bool) :
    lateOpeningPublicAnswerReward assessment false .withheld (.failure guess) =
      if guess then 9 / 20 else 11 / 20 := by
  classical
  rw [lateOpeningPublicAnswerReward, expect]
  change (∑' history : (lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo false .withheld),
    (assessment.belief .listener (lateOpeningPublicListenerSite G false .withheld)
      history).toReal * lateLeakStatePayoff G .listener
        (lateLeakAnswered history.1.state (some (.reply (.failure guess))))) = _
  rw [← (lateOpeningPublicWithheldFiberEquiv G).tsum_eq]
  simp only [lateOpeningPublicWithheldFiberEquiv, Equiv.ofBijective_apply, prior]
  simp only [lateOpeningPublicWithheldMember, lateOpeningPublicAnswerHistory_state,
    lateLeakAnswered, lateLeakReplyOf, lateLeakStatePayoff, lateLeakListenerPayoff,
    LateLeakResolution.succeeded, Bool.false_eq_true, ite_false]
  have card : Fintype.card LateLeakLabel = 3 := rfl
  cases guess <;>
    norm_num [lateLeakPrior, PMF.ofFintype_apply, tsum_fintype,
      Fintype.sum_prod_type, Fintype.sum_bool, card]

/-- Every genuine listener information site is one of the recorded public
resolution fibers. No sites are removed because they are unreached. -/
theorem lateOpeningPublic_listener_site
    (site : (lateOpeningPublicModel G).InformationSite .listener) :
    ∃ bit resolution, site = lateOpeningPublicListenerSite G bit resolution ∧
      (resolution = .withheld → bit = false) := by
  obtain ⟨history, running, move, permitted⟩ := site.2
  have old : some move ∈ lateLeakMenu true (lateLeakView .listener history.1.state) := by
    change some move ∈ lateLeakMenu true site.1.1.1 at permitted
    rw [← history.2, lateOpeningPublic_old_info_projection, lateLeak_infoOf] at permitted
    exact permitted
  cases history with
  | mk history observed =>
    rcases history with ⟨state, trace⟩
    cases state with
    | answering secret resolution =>
      let bit := if resolution = .withheld then false else secret.1
      refine ⟨bit, resolution, Subtype.ext ?_, ?_⟩
      · rw [← observed, lateOpeningPublic_listener_info_answering]
        cases resolution <;> rfl
      · intro withheld
        simp [bit, withheld]
    | _ => simp [lateLeakView, lateLeakMenu] at old

/-- Native sequential rationality at the final listener decision follows from
the explicit public Bayes beliefs, including the withholding fiber. -/
theorem lateOpeningPublic_listener_rational
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment)
    (canonical : assessment.strategy = lateOpeningPublicCanonical G)
    (uniform : ∀ bit resolution first second,
      assessment.belief .listener (lateOpeningPublicListenerSite G bit resolution)
          (lateOpeningPublicAnswerMember G bit resolution first) =
        assessment.belief .listener (lateOpeningPublicListenerSite G bit resolution)
          (lateOpeningPublicAnswerMember G bit resolution second))
    (prior : ∀ secret, assessment.belief .listener
      (lateOpeningPublicListenerSite G false .withheld)
      (lateOpeningPublicWithheldMember G secret) = lateLeakPrior secret)
    (site : (lateOpeningPublicModel G).InformationSite .listener) :
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext (lateLeak_terminates G true) site
        (lateLeakPayoff G true .listener)) := by
  classical
  obtain ⟨bit, resolution, rfl, withheld_bit⟩ := lateOpeningPublic_listener_site site
  let decision := lateOpeningPublicListenerDecision G bit resolution (assessment.strategy .listener)
  apply (decision.rationalAt_iff_support_maximal assessment).mpr
  intro chosen supported alternative
  have canonicalLaw : (lateOpeningPublicCanonical G .listener
      (lateOpeningPublicListenerInfo bit resolution)).map Subtype.val =
      PMF.pure (some (.reply (lateOpeningPublicReply (bit, .a) resolution))) := by
    cases resolution <;>
      simp [PMF.pure_map, lateOpeningPublicCanonical, lateOpeningPublicReply,
        lateOpeningPublicListenerInfo, lateOpeningPublicTranscript,
        lateLeakSignal, LateLeakSignal.success, LateLeakResolution.succeeded]
  have chosen_value : chosen.1 =
      some (.reply (lateOpeningPublicReply (bit, .a) resolution)) := by
    have mapped : chosen.1 ∈ ((assessment.strategy .listener
        (lateOpeningPublicListenerInfo bit resolution)).map Subtype.val).support := by
      rw [PMF.support_map]
      exact ⟨chosen, supported, rfl⟩
    rw [canonical, canonicalLaw, PMF.mem_support_pure_iff] at mapped
    exact mapped
  obtain ⟨answer, alternative_value, fits⟩ := alternative.2
  rw [lateOpeningPublicListenerDecision_expectedReward assessment bit resolution _
      alternative answer alternative_value,
    lateOpeningPublicListenerDecision_expectedReward assessment bit resolution _
      chosen _ chosen_value]
  change answer.fits (lateLeakSignal (bit, .a) resolution) at fits
  by_cases withheld : resolution = .withheld
  · subst resolution
    have equal := withheld_bit rfl
    subst bit
    cases answer with
    | failure guess =>
      rw [lateOpeningPublicReply]
      simp only [LateLeakResolution.succeeded, Bool.false_eq_true, ite_false, ite_true]
      rw [lateOpeningPublic_withheld_reward assessment prior guess,
        lateOpeningPublic_withheld_reward assessment prior false]
      cases guess <;> norm_num
    | _ => simp [LateLeakAnswer.fits, lateLeakSignal, LateLeakSignal.success] at fits
  · by_cases success : resolution.succeeded = true
    · have safe := lateOpeningPublic_success_safe_reward assessment bit resolution success
      simp only [lateOpeningPublicReply, success, ite_true]
      rw [safe]
      cases answer with
      | safe => rw [safe]
      | guess label =>
        rw [lateOpeningPublic_success_guess_reward assessment bit resolution withheld success,
          lateOpeningPublic_emitted_belief_uniform assessment bit resolution withheld
            (uniform bit resolution)]
        norm_num
      | failure guess =>
        cases resolution <;>
          simp_all [LateLeakAnswer.fits, lateLeakSignal, LateLeakSignal.success,
            LateLeakResolution.succeeded]
    · have failed : resolution.succeeded = false := Bool.eq_false_iff.mpr success
      simp only [lateOpeningPublicReply, failed, withheld, Bool.false_eq_true, ite_false]
      rw [lateOpeningPublic_failed_emission_reward assessment bit resolution withheld failed bit]
      simp only [ite_true]
      cases answer with
      | failure guess =>
        rw [lateOpeningPublic_failed_emission_reward assessment bit resolution withheld failed]
        split_ifs <;> norm_num
      | _ =>
        cases resolution <;>
          simp_all [LateLeakAnswer.fits, lateLeakSignal, LateLeakSignal.success,
            LateLeakResolution.succeeded]

/-- Complete public traffic admits a genuine sequential equilibrium with
protected transmission, safe successful replies, and truthful failed replies.
The assumptions compare actual payoffs, rather than prescribing beliefs. -/
theorem lateOpeningPublic_exists_sequential_equilibrium (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (cost : G.reward / 2 < G.forfeit + G.dropCharge)
    (margin : 0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
      G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge) :
    ∃ assessment : (lateOpeningPublicModel G).BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      assessment.strategy = lateOpeningPublicCanonical G := by
  classical
  obtain ⟨original, consistent, agrees, uniform, prior⟩ :=
    lateOpeningPublicCanonical_consistent_public_beliefs G
  let assessment : (lateOpeningPublicModel G).BehavioralAssessment :=
    ⟨lateOpeningPublicCanonical G, original.belief⟩
  refine ⟨assessment, ⟨?_, ?_⟩, rfl⟩
  · intro who site
    cases who with
    | sender =>
      apply (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
        (fun _ _ => payoffIntegrable_of_finite _ _)).mpr
      intro alternative _
      exact lateOpeningPublic_sender_context_best_response G reward cost margin
        assessment rfl site alternative
    | listener =>
      exact lateOpeningPublic_listener_rational assessment rfl uniform prior site
  · obtain ⟨sequence, approximate, converges⟩ := consistent
    refine ⟨sequence, approximate, ?_, converges.2⟩
    intro who site
    change PMFConvergesPointwise _ (lateOpeningPublicCanonical G who site.1)
    rw [← agrees who site]
    exact converges.1 who site

/-- The original impossibility parameters themselves admit a preserving
sequential equilibrium once failed second emissions remain publicly visible. -/
theorem lateOpeningPublic_deferral_pays_sequential_equilibrium (G : LateLeakParameters)
    (incentives : G.DeferralPays) (charge : 0 ≤ G.dropCharge) :
    ∃ assessment : (lateOpeningPublicModel G).BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      assessment.strategy = lateOpeningPublicCanonical G := by
  obtain ⟨cost, margin⟩ := lateOpeningPublic_margins_of_deferral_pays G incentives charge
  exact lateOpeningPublic_exists_sequential_equilibrium G incentives.reward_pos.le cost margin

private theorem canonical_initial_kernel (G : LateLeakParameters) :
    lateOpeningPublicKernel G (lateOpeningPublicCanonical G) .initial =
      lateLeakPrior.map LateLeakState.protectedTurn := by
  change lateOpeningPublicKernel G (lateOpeningPublicCanonical G)
    (lateLeakExecution G true).initHistory.state = _
  rw [lateOpeningPublicKernel_move_law G (lateOpeningPublicCanonical G)
    (lateLeakExecution G true).initHistory (by change ¬False; exact not_false), PMF.bind_map]
  change (_ : PMF _).bind (fun _ => lateLeakPrior.map LateLeakState.protectedTurn) = _
  exact PMF.bind_const _ _

private theorem canonical_protected_kernel (G : LateLeakParameters) (secret : LateLeakType) :
    lateOpeningPublicKernel G (lateOpeningPublicCanonical G) (.protectedTurn secret) =
      PMF.pure (.answering secret .protectedOpen) := by
  change lateOpeningPublicKernel G (lateOpeningPublicCanonical G)
    (lateLeakTypeHistory G true secret).state = _
  rw [lateOpeningPublicKernel_move_law G (lateOpeningPublicCanonical G)
    (lateLeakTypeHistory G true secret) (by change ¬False; exact not_false)]
  change (((lateOpeningPublicCanonical G .sender)
    ((lateOpeningPublicModel G).infoOf .sender (lateLeakTypeHistory G true secret).trace)).map
      Subtype.val).bind (lateLeakAdvance G (.protectedTurn secret)) = _
  rw [lateOpeningPublicCanonical_opening_law G secret _ (Or.inl rfl), PMF.pure_bind]
  simp [lateLeakAdvance]

private theorem canonical_protected_answer_kernel (G : LateLeakParameters)
    (secret : LateLeakType) :
    lateOpeningPublicKernel G (lateOpeningPublicCanonical G) (.answering secret .protectedOpen) =
      PMF.pure (.finished secret .protectedOpen .safe) := by
  change lateOpeningPublicKernel G (lateOpeningPublicCanonical G)
    (lateLeakOpenedHistory G true secret).state = _
  rw [lateOpeningPublicKernel_move_law G (lateOpeningPublicCanonical G)
    (lateLeakOpenedHistory G true secret) (by change ¬False; exact not_false)]
  change (((lateOpeningPublicCanonical G .listener)
    ((lateOpeningPublicModel G).infoOf .listener (lateLeakOpenedHistory G true secret).trace)).map
      Subtype.val).bind (lateLeakAdvance G (.answering secret .protectedOpen)) = _
  rw [lateOpeningPublicCanonical_answer_law, PMF.pure_bind]
  simp [lateLeakAdvance, lateLeakReplyOf, lateOpeningPublicReply, LateLeakResolution.succeeded]

private theorem public_iterate_finished (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (fuel : ℕ) (secret : LateLeakType)
    (resolution : LateLeakResolution) (answer : LateLeakAnswer) :
    (fun law => law.bind (lateOpeningPublicKernel G profile))^[fuel]
      (PMF.pure (.finished secret resolution answer)) =
      PMF.pure (.finished secret resolution answer) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply, PMF.pure_bind,
      lateOpeningPublicKernel_terminal G profile (.finished secret resolution answer)
        (by trivial), ih]

/-- Canonical native execution preserves the complete intended terminal-state
law, including the initially sampled private type. -/
theorem lateOpeningPublicCanonical_intended_outcome (G : LateLeakParameters) :
    ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
      (lateOpeningPublicCanonical G) (lateLeakExecution G true).initHistory).map
        ExecutionProtocol.History.state = lateLeakIntendedOutcome := by
  rw [lateOpeningPublic_terminal_map_state, Function.iterate_succ_apply, PMF.pure_bind]
  change (fun law => law.bind (lateOpeningPublicKernel G (lateOpeningPublicCanonical G)))^[4]
    (lateOpeningPublicKernel G (lateOpeningPublicCanonical G) .initial) = _
  rw [canonical_initial_kernel, ← PMF.bind_pure_comp, iterate_bind,
    lateLeakIntendedOutcome, ← PMF.bind_pure_comp]
  congr 1
  funext secret
  dsimp only [Function.comp_apply]
  rw [Function.iterate_succ_apply, PMF.pure_bind, canonical_protected_kernel,
    Function.iterate_succ_apply, PMF.pure_bind, canonical_protected_answer_kernel,
    public_iterate_finished]

/-- Every equilibrium of the original intended game has its full observable
state law preserved by an equilibrium with complete public opening traffic.
This comparison theorem does not assert a raw Vegas source-program adapter. -/
theorem lateOpeningPublic_preserves_intended_sequential_equilibria (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (cost : G.reward / 2 < G.forfeit + G.dropCharge)
    (margin : 0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
      G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge)
    (source : (lateLeakModel G false).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium (lateLeak_antichain G false)
      (lateLeak_terminates G false) (lateLeakPayoff G false)) :
    ∃ target : (lateOpeningPublicModel G).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
        target.strategy (lateLeakExecution G true).initHistory).map
          ExecutionProtocol.History.state = lateLeakOutcomeLaw G false source.strategy := by
  obtain ⟨target, targetEquilibrium, canonical⟩ :=
    lateOpeningPublic_exists_sequential_equilibrium G reward cost margin
  refine ⟨target, targetEquilibrium, ?_⟩
  rw [canonical, lateOpeningPublicCanonical_intended_outcome,
    lateLeak_intended_outcome source equilibrium]

end Vegas
