/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.CompleteObservationPreservation
import Vegas.Examples.LateLeak.CompleteObservationProtectedPosterior
import GameTheory.Analysis.Protocol.SupportedChoices
import GameTheory.Analysis.Protocol.SequentialExistence
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Failure-cost preservation with complete public traffic

Bounds on the actual finite continuation kernels control every adaptive policy.
Low inclusion probabilities make protected opening strictly better independently
of off-path beliefs; the explicit public equilibrium covers high probabilities.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : LateLeakParameters}

def lateOpeningPublicSuccessUpper (G : LateLeakParameters) (secret : LateLeakType) : ℝ :=
  if secret.2 = .c then G.reward / 2 else G.reward

def lateOpeningPublicFailureUpper (G : LateLeakParameters) (secret : LateLeakType)
    (resolution : LateLeakResolution) : ℝ :=
  (if secret.2 = .c then 0 else G.reward) - G.forfeit -
    (if resolution.droppedLate then G.dropCharge else 0)

def lateOpeningPublicReplyUpper (G : LateLeakParameters) (secret : LateLeakType)
    (resolution : LateLeakResolution) : ℝ :=
  if resolution.succeeded then lateOpeningPublicSuccessUpper G secret
  else lateOpeningPublicFailureUpper G secret resolution

def lateOpeningPublicDeferralUpper (G : LateLeakParameters) (secret : LateLeakType) : ℝ :=
  max (lateOpeningPublicFailureUpper G secret .withheld)
    (lateLeakInclusionProb G * lateOpeningPublicSuccessUpper G secret +
      (1 - lateLeakInclusionProb G) * lateOpeningPublicFailureUpper G secret .secondDropped)

def lateOpeningPublicProtectedLower (G : LateLeakParameters) (secret : LateLeakType) : ℝ :=
  if secret.2 = .c then 0 else G.reward / 2

theorem lateOpeningPublic_reply_payoff_upper (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (secret : LateLeakType) (resolution : LateLeakResolution)
    (answer : LateLeakAnswer) :
    lateLeakSenderPayoff G secret resolution answer ≤
      lateOpeningPublicReplyUpper G secret resolution := by
  rcases secret with ⟨bit, label⟩
  cases label <;> cases resolution <;> cases answer <;> casesm* Bool <;>
    simp only [lateLeakSenderPayoff, lateLeakSenderBase, lateOpeningPublicReplyUpper,
      lateOpeningPublicFailureUpper, lateOpeningPublicSuccessUpper,
      LateLeakResolution.succeeded, LateLeakResolution.droppedLate,
      reduceCtorEq, ite_true, ite_false, sub_zero]
  all_goals linarith

theorem lateOpeningPublic_protected_payoff_lower (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (secret : LateLeakType) (answer : LateLeakAnswer)
    (fits : answer.fits (lateLeakSignal secret .protectedOpen)) :
    lateOpeningPublicProtectedLower G secret ≤
      lateLeakSenderPayoff G secret .protectedOpen answer := by
  rcases secret with ⟨bit, label⟩
  cases label <;> cases answer <;>
    simp_all [lateOpeningPublicProtectedLower, lateLeakSenderPayoff, lateLeakSenderBase,
      LateLeakAnswer.fits, lateLeakSignal, LateLeakSignal.success,
      LateLeakResolution.succeeded, LateLeakResolution.droppedLate]
  all_goals linarith

theorem lateOpeningPublic_deferral_le_success (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (forfeit : 0 ≤ G.forfeit) (charge : 0 ≤ G.dropCharge)
    (secret : LateLeakType) :
    lateOpeningPublicDeferralUpper G secret ≤ lateOpeningPublicSuccessUpper G secret := by
  have q0 := (lateLeakInclusionProb_pos G).le
  have q1 := (lateLeakInclusionProb_lt_one G).le
  have failed : lateOpeningPublicFailureUpper G secret .withheld ≤
      lateOpeningPublicSuccessUpper G secret := by
    rcases secret with ⟨bit, label⟩
    cases label <;>
      simp [lateOpeningPublicFailureUpper, lateOpeningPublicSuccessUpper,
        LateLeakResolution.droppedLate] <;> linarith
  have dropped : lateOpeningPublicFailureUpper G secret .secondDropped ≤
      lateOpeningPublicSuccessUpper G secret := by
    rcases secret with ⟨bit, label⟩
    cases label <;>
      simp [lateOpeningPublicFailureUpper, lateOpeningPublicSuccessUpper,
        LateLeakResolution.droppedLate] <;> linarith
  apply max_le failed
  nlinarith [mul_le_mul_of_nonneg_left dropped (sub_nonneg.mpr q1)]

def lateOpeningPublicUpperPotential (G : LateLeakParameters) : LateLeakState → ℝ
  | .initial => G.reward
  | .protectedTurn secret => lateOpeningPublicSuccessUpper G secret
  | .firstLate secret | .secondLate secret => lateOpeningPublicDeferralUpper G secret
  | .answering secret resolution => lateOpeningPublicReplyUpper G secret resolution
  | .finished secret resolution answer => lateLeakSenderPayoff G secret resolution answer

private theorem public_choice_menu (G : LateLeakParameters) (who : LateLeakRole)
    (history : (lateLeakExecution G true).History)
    (choice : (lateOpeningPublicModel G).Choice who
      ((lateOpeningPublicModel G).infoOf who history.trace)) :
    choice.1 ∈ lateLeakMenu true (lateLeakView who history.state) := by
  have allowed := choice.2
  change choice.1 ∈ lateLeakMenu true
    (((lateOpeningPublicModel G).infoOf who history.trace).1.1) at allowed
  rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf] at allowed
  exact allowed

private theorem public_transmission_upper (G : LateLeakParameters) (secret : LateLeakType)
    (state : LateLeakState)
    (turn : state = .firstLate secret ∨ state = .secondLate secret) :
    expect (lateLeakAdvance G state (some (.opening true)))
      (lateOpeningPublicUpperPotential G) ≤ lateOpeningPublicDeferralUpper G secret := by
  rcases turn with rfl | rfl <;>
    simp only [lateLeakAdvance, ite_true, expect_map]
  all_goals rw [lateLeak_expect_inclusion]
  all_goals exact le_max_right _ _

/-- Every actual native one-step law respects a type-sensitive payoff bound,
regardless of the profile's private recall, traffic observations or beliefs. -/
theorem lateOpeningPublic_upper_step (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (forfeit : 0 ≤ G.forfeit) (charge : 0 ≤ G.dropCharge)
    (profile : LateOpeningPublicProfile G) (history : (lateLeakExecution G true).History) :
    expect (lateOpeningPublicKernel G profile history.state) (lateOpeningPublicUpperPotential G) ≤
      lateOpeningPublicUpperPotential G history.state := by
  classical
  rcases history with ⟨state, trace⟩
  cases state with
  | finished secret resolution answer =>
    rw [lateOpeningPublicKernel_terminal G profile _ (by trivial), expect_pure]
  | initial =>
    rw [lateOpeningPublicKernel_move_law G profile ⟨_, trace⟩
      (by change ¬False; exact not_false), PMF.bind_map]
    change expect ((_ : PMF _).bind (fun _ => lateLeakPrior.map LateLeakState.protectedTurn)) _ ≤ _
    rw [PMF.bind_const, expect_map]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
    intro secret _
    rcases secret with ⟨bit, label⟩
    cases label <;> simp only [Function.comp_apply, lateOpeningPublicUpperPotential,
      lateOpeningPublicSuccessUpper, reduceCtorEq, ite_true, ite_false]
    all_goals linarith
  | answering secret resolution =>
    rw [lateOpeningPublicKernel_move_law G profile ⟨_, trace⟩ (by change ¬False; exact not_false),
      PMF.bind_map, expect_bind_of_finite]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
    intro choice _
    dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
    simp only [lateLeakAdvance, expect_pure, lateOpeningPublicUpperPotential]
    exact lateOpeningPublic_reply_payoff_upper G reward secret resolution _
  | protectedTurn secret =>
    rw [lateOpeningPublicKernel_move_law G profile ⟨_, trace⟩ (by change ¬False; exact not_false),
      PMF.bind_map, expect_bind_of_finite]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
    intro choice _
    dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
    obtain ⟨now, same, _⟩ := public_choice_menu G .sender ⟨_, trace⟩ choice
    rw [same]
    cases now
    · simpa [lateLeakAdvance, expect_pure, lateOpeningPublicUpperPotential] using
        lateOpeningPublic_deferral_le_success G reward forfeit charge secret
    · simp [lateLeakAdvance, expect_pure, lateOpeningPublicUpperPotential,
        lateOpeningPublicReplyUpper, LateLeakResolution.succeeded]
  | firstLate secret =>
    rw [lateOpeningPublicKernel_move_law G profile ⟨_, trace⟩ (by change ¬False; exact not_false),
      PMF.bind_map, expect_bind_of_finite]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
    intro choice _
    dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
    obtain ⟨now, same⟩ := public_choice_menu G .sender ⟨_, trace⟩ choice
    rw [same]
    cases now
    · simp [lateLeakAdvance, expect_pure, lateOpeningPublicUpperPotential]
    · exact public_transmission_upper G secret _ (Or.inl rfl)
  | secondLate secret =>
    rw [lateOpeningPublicKernel_move_law G profile ⟨_, trace⟩ (by change ¬False; exact not_false),
      PMF.bind_map, expect_bind_of_finite]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
    intro choice _
    dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
    obtain ⟨now, same⟩ := public_choice_menu G .sender ⟨_, trace⟩ choice
    rw [same]
    cases now
    · simp [lateLeakAdvance, expect_pure, lateOpeningPublicUpperPotential,
        lateOpeningPublicReplyUpper, lateOpeningPublicDeferralUpper,
        LateLeakResolution.succeeded]
    · exact public_transmission_upper G secret _ (Or.inr rfl)

/-- The actual whole terminal sender payoff is bounded under every behavioral
profile, so the estimate covers arbitrary adaptive late responses. -/
theorem lateOpeningPublic_sender_payoff_upper (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (forfeit : 0 ≤ G.forfeit) (charge : 0 ≤ G.dropCharge)
    (profile : LateOpeningPublicProfile G) (history : (lateLeakExecution G true).History) :
    expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
      profile history) (lateLeakPayoff G true .sender) ≤
      lateOpeningPublicUpperPotential G history.state := by
  classical
  have one (state : LateLeakState) :
      expect (lateOpeningPublicKernel G profile state) (lateOpeningPublicUpperPotential G) ≤
        lateOpeningPublicUpperPotential G state := by
    by_cases reached : Nonempty ((lateLeakExecution G true).Trace state)
    · exact lateOpeningPublic_upper_step G reward forfeit charge profile
        ⟨state, Classical.choice reached⟩
    · by_cases stopped : state.IsFinished
      · simp [lateOpeningPublicKernel, stopped, expect_pure]
      · simp [lateOpeningPublicKernel, stopped, reached, expect_pure]
  have iterate (fuel : ℕ) :
      expect ((fun law => law.bind (lateOpeningPublicKernel G profile))^[fuel]
        (PMF.pure history.state)) (lateOpeningPublicUpperPotential G) ≤
          lateOpeningPublicUpperPotential G history.state := by
    induction fuel with
    | zero => simp [expect_pure]
    | succ fuel ih =>
      rw [Function.iterate_succ_apply', expect_bind_of_finite]
      exact (expect_mono (fun state _ => one state) (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _)).trans ih
  have terminal : expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom
        (lateLeak_terminates G true) profile history) (lateLeakPayoff G true .sender) =
      expect (((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
        profile history).map ExecutionProtocol.History.state)
          (lateOpeningPublicUpperPotential G) := by
    rw [expect_map]
    apply expect_congr_on_support
    intro final supported
    have stopped := (lateOpeningPublicModel G).runBehavioralTerminalFrom_support_terminal
      (lateLeak_terminates G true) profile history final supported
    rcases final with ⟨state, trace⟩
    cases state with
    | finished secret resolution answer => rfl
    | _ => exact stopped.elim
  rw [terminal, lateOpeningPublic_terminal_map_state]
  exact iterate 5

def lateOpeningPublicProtectedSenderSite (G : LateLeakParameters) (secret : LateLeakType) :
    (lateOpeningPublicModel G).InformationSite .sender :=
  ⟨(lateOpeningPublicModel G).infoOf .sender (lateLeakTypeHistory G true secret).trace,
    ⟨⟨lateLeakTypeHistory G true secret, rfl⟩,
      (by change ¬False; exact not_false), .opening true, by
      change some (.opening true) ∈ lateLeakMenu true
        (((lateOpeningPublicModel G).infoOf .sender
          (lateLeakTypeHistory G true secret).trace).1.1)
      rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf]
      exact lateLeak_open_allowed true secret⟩⟩

def lateOpeningPublicProtectedChoice (G : LateLeakParameters) (secret : LateLeakType)
    (now : Bool) : (lateOpeningPublicModel G).Choice .sender
      (lateOpeningPublicProtectedSenderSite G secret).1 :=
  ⟨some (.opening now), by
    change some (.opening now) ∈ lateLeakMenu true
      (((lateOpeningPublicModel G).infoOf .sender
        (lateLeakTypeHistory G true secret).trace).1.1)
    rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf]
    exact ⟨now, rfl, by simp⟩⟩

theorem lateOpeningPublic_protected_fiber_history (G : LateLeakParameters)
    (secret : LateLeakType)
    (history : (lateOpeningPublicModel G).InformationHistory .sender
      (lateOpeningPublicProtectedSenderSite G secret).1) :
    history.1 = lateLeakTypeHistory G true secret := by
  have view := congrArg (fun info => info.1.1) history.2
  change ((lateOpeningPublicModel G).infoOf .sender history.1.trace).1.1 =
    ((lateOpeningPublicModel G).infoOf .sender
      (lateLeakTypeHistory G true secret).trace).1.1 at view
  rw [lateOpeningPublic_old_info_projection, lateOpeningPublic_old_info_projection,
    lateLeak_infoOf, lateLeak_infoOf] at view
  change LateLeakView.full history.1.state = .full (.protectedTurn secret) at view
  exact lateLeak_history_eq_of_state_eq (LateLeakView.full.inj view)

/-- A protected committed response advances along its actual native history,
without replacing any later adaptive behavior. -/
theorem lateOpeningPublic_protected_committed_continuation (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (secret : LateLeakType) (now : Bool) :
    let changed : LateOpeningPublicProfile G :=
      Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature) profile .sender
        ((profile .sender).commit (lateOpeningPublicProtectedSenderSite G secret).1
          (lateOpeningPublicProtectedChoice G secret now))
    (lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
        changed (lateLeakTypeHistory G true secret) =
      (lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
        changed (if now then lateLeakOpenedHistory G true secret
          else lateLeakFirstHistory G secret) := by
  classical
  intro changed
  have one : (lateOpeningPublicModel G).runBehavioralFrom changed 1
      (lateLeakTypeHistory G true secret) =
      PMF.pure (if now then lateLeakOpenedHistory G true secret
        else lateLeakFirstHistory G secret) := by
    apply pmf_map_injective (f := ExecutionProtocol.History.state)
      (fun first second same => lateLeak_history_eq_of_state_eq same)
    rw [lateOpeningPublic_run_map_state]
    simp only [Function.iterate_one, PMF.pure_bind, PMF.pure_map]
    rw [lateOpeningPublicKernel_move_law G changed (lateLeakTypeHistory G true secret)
      (by change ¬False; exact not_false)]
    change (((changed .sender) (lateOpeningPublicProtectedSenderSite G secret).1).map
      Subtype.val).bind (lateLeakAdvance G (.protectedTurn secret)) = _
    simp only [changed, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
      PMF.pure_map, PMF.pure_bind]
    cases now <;> rfl
  rw [(lateOpeningPublicModel G).runBehavioralTerminalFrom_eq_bind_runBehavioralFrom
    (lateLeak_terminates G true) changed 1, one, PMF.pure_bind]

theorem lateOpeningPublic_protected_commit_wait_upper (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (forfeit : 0 ≤ G.forfeit) (charge : 0 ≤ G.dropCharge)
    (profile : LateOpeningPublicProfile G) (secret : LateLeakType) :
    expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
      (Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature) profile .sender
        ((profile .sender).commit (lateOpeningPublicProtectedSenderSite G secret).1
          (lateOpeningPublicProtectedChoice G secret false)))
      (lateLeakTypeHistory G true secret)) (lateLeakPayoff G true .sender) ≤
        lateOpeningPublicDeferralUpper G secret := by
  rw [lateOpeningPublic_protected_committed_continuation]
  exact lateOpeningPublic_sender_payoff_upper G reward forfeit charge _ _

theorem lateOpeningPublic_protected_commit_open_lower (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (profile : LateOpeningPublicProfile G) (secret : LateLeakType) :
    lateOpeningPublicProtectedLower G secret ≤
      expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
        (Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature) profile .sender
          ((profile .sender).commit (lateOpeningPublicProtectedSenderSite G secret).1
            (lateOpeningPublicProtectedChoice G secret true)))
        (lateLeakTypeHistory G true secret)) (lateLeakPayoff G true .sender) := by
  rw [lateOpeningPublic_protected_committed_continuation]
  change _ ≤ expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom
    (lateLeak_terminates G true) _
      ⟨.answering secret .protectedOpen, (lateLeakOpenedHistory G true secret).trace⟩) _
  rw [lateOpeningPublic_answering_continuation_value]
  rw [← expect_constant _ (lateOpeningPublicProtectedLower G secret)]
  apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  intro choice _
  obtain ⟨answer, same, fits⟩ := public_choice_menu G .listener
    (lateLeakOpenedHistory G true secret) choice
  rw [same]
  exact lateOpeningPublic_protected_payoff_lower G reward secret answer fits

/-- The strict cost gap controls every native sender assessment and every
whole continuation policy, including arbitrary public-traffic conditioning. -/
theorem lateOpeningPublic_rational_protected_pure (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (forfeit : 0 ≤ G.forfeit) (charge : 0 ≤ G.dropCharge)
    (gap : ∀ secret, lateOpeningPublicDeferralUpper G secret <
      lateOpeningPublicProtectedLower G secret)
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational (lateLeak_terminates G true)
      (lateLeakPayoff G true)) (secret : LateLeakType) :
    assessment.strategy .sender (lateOpeningPublicProtectedSenderSite G secret).1 =
      PMF.pure (lateOpeningPublicProtectedChoice G secret true) := by
  classical
  let site := lateOpeningPublicProtectedSenderSite G secret
  have nonterminal : site.AllNonterminal := by
    intro history
    rw [lateOpeningPublic_protected_fiber_history G secret history]
    change ¬False
    exact not_false
  have unsupported : lateOpeningPublicProtectedChoice G secret false ∉
      (assessment.strategy .sender site.1).support := by
    apply assessment.not_supported_choice_of_uniform_gap
      ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)) site
      ((lateOpeningPublicModel G).runnerFactorsAt_terminal (lateLeak_terminates G true)
        (lateOpeningPublicModel_decisionRecall G).actsOnceWhereItMatters nonterminal)
      (lateLeakPayoff G true .sender) (rational .sender site)
      (payoffIntegrable_of_finite _ _) (lateOpeningPublicProtectedChoice G secret false)
      ((assessment.strategy .sender).commit site.1 (lateOpeningPublicProtectedChoice G secret true))
      (payoffIntegrable_of_finite _ _)
      (lateOpeningPublicDeferralUpper G secret) (lateOpeningPublicProtectedLower G secret)
      (gap secret)
    · intro history
      rw [lateOpeningPublic_protected_fiber_history G secret history]
      exact lateOpeningPublic_protected_commit_wait_upper G reward forfeit charge _ secret
    · intro history
      rw [lateOpeningPublic_protected_fiber_history G secret history]
      exact lateOpeningPublic_protected_commit_open_lower G reward _ secret
  apply pmf_eq_pure_of_support_subset_singleton
  intro choice supported
  have permitted := choice.2
  change choice.1 ∈ lateLeakMenu true
    (((lateOpeningPublicModel G).infoOf .sender
      (lateLeakTypeHistory G true secret).trace).1.1) at permitted
  rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf] at permitted
  obtain ⟨now, same, _⟩ := permitted
  cases now
  · have equal : choice = lateOpeningPublicProtectedChoice G secret false := Subtype.ext same
    exact (unsupported (equal ▸ supported)).elim
  · exact Subtype.ext same

/-- A fixed forfeit of twice the positive reward gives the strict gap for
every inclusion probability below three quarters, without a drop charge. -/
theorem lateOpeningPublic_twice_reward_gap (G : LateLeakParameters)
    (reward : 0 < G.reward) (forfeit : G.forfeit = 2 * G.reward) (charge : G.dropCharge = 0)
    (low : lateLeakInclusionProb G < 3 / 4) (secret : LateLeakType) :
    lateOpeningPublicDeferralUpper G secret < lateOpeningPublicProtectedLower G secret := by
  have q0 := lateLeakInclusionProb_pos G
  have margin : 0 < (3 / 4 - lateLeakInclusionProb G) * G.reward :=
    mul_pos (sub_pos.mpr low) reward
  rcases secret with ⟨bit, label⟩
  cases label <;>
    simp only [lateOpeningPublicDeferralUpper, lateOpeningPublicFailureUpper,
      lateOpeningPublicSuccessUpper, lateOpeningPublicProtectedLower,
      LateLeakResolution.droppedLate, Bool.false_eq_true, ite_false, ite_true,
      forfeit, charge] <;>
    apply max_lt <;> norm_num <;> nlinarith

private theorem protected_rational_safe (G : LateLeakParameters)
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational (lateLeak_terminates G true)
      (lateLeakPayoff G true)) (bit : Bool)
    (uniform : ∀ first second, assessment.belief .listener
        (lateOpeningPublicListenerSite G bit .protectedOpen)
        (lateOpeningPublicAnswerMember G bit .protectedOpen first) =
      assessment.belief .listener (lateOpeningPublicListenerSite G bit .protectedOpen)
        (lateOpeningPublicAnswerMember G bit .protectedOpen second)) :
    (assessment.strategy .listener (lateOpeningPublicListenerInfo bit .protectedOpen)).map
      Subtype.val = PMF.pure (some (.reply .safe)) := by
  classical
  let decision := lateOpeningPublicListenerDecision G bit .protectedOpen
    (assessment.strategy .listener)
  have fitsSafe : LateLeakAnswer.safe.fits (lateLeakSignal (bit, .a) .protectedOpen) := rfl
  let safe : (lateOpeningPublicModel G).Choice .listener
      (lateOpeningPublicListenerInfo bit .protectedOpen) :=
    ⟨some (.reply .safe), ⟨.safe, rfl, fitsSafe⟩⟩
  have pure : assessment.strategy .listener (lateOpeningPublicListenerInfo bit .protectedOpen) =
      PMF.pure safe := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro choice supported
    obtain ⟨answer, same, fits⟩ := choice.2
    have optimal := decision.rational_support_maximal assessment
      ((assessment.isSequentiallyRational_iff_with _ _).mp rational) choice supported safe
    rw [lateOpeningPublicListenerDecision_expectedReward assessment bit .protectedOpen _
        safe .safe rfl,
      lateOpeningPublicListenerDecision_expectedReward assessment bit .protectedOpen _
        choice answer same,
      lateOpeningPublic_success_safe_reward assessment bit .protectedOpen rfl] at optimal
    cases answer with
    | safe => exact Subtype.ext same
    | guess label =>
      rw [lateOpeningPublic_success_guess_reward assessment bit .protectedOpen (by decide) rfl,
        lateOpeningPublic_emitted_belief_uniform assessment bit .protectedOpen (by decide)
          uniform] at optimal
      norm_num at optimal
    | failure guess =>
      simp [LateLeakAnswer.fits, lateLeakSignal, LateLeakSignal.success] at fits
  rw [pure, PMF.pure_map]

/-- Sure protected transmission and safe protected replies determine the full
initialized state law independently of every later or unreached response. -/
theorem lateOpeningPublic_intended_outcome_of_protected_safe (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G)
    (opens : ∀ secret,
      ((profile .sender) ((lateOpeningPublicModel G).infoOf .sender
        (lateLeakTypeHistory G true secret).trace)).map Subtype.val =
          PMF.pure (some (.opening true)))
    (safe : ∀ bit, (profile .listener
      (lateOpeningPublicListenerInfo bit .protectedOpen)).map Subtype.val =
        PMF.pure (some (.reply .safe))) :
    ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
      profile (lateLeakExecution G true).initHistory).map ExecutionProtocol.History.state =
        lateLeakIntendedOutcome := by
  have protectedKernel (secret : LateLeakType) :
      lateOpeningPublicKernel G profile (.protectedTurn secret) =
        PMF.pure (.answering secret .protectedOpen) := by
    change lateOpeningPublicKernel G profile (lateLeakTypeHistory G true secret).state = _
    rw [lateOpeningPublicKernel_move_law G profile (lateLeakTypeHistory G true secret)
      (by change ¬False; exact not_false)]
    change (((profile .sender) ((lateOpeningPublicModel G).infoOf .sender
      (lateLeakTypeHistory G true secret).trace)).map Subtype.val).bind
        (lateLeakAdvance G (.protectedTurn secret)) = _
    rw [opens, PMF.pure_bind]
    simp [lateLeakAdvance]
  have answered (secret : LateLeakType) :
      lateOpeningPublicKernel G profile (.answering secret .protectedOpen) =
        PMF.pure (.finished secret .protectedOpen .safe) := by
    change lateOpeningPublicKernel G profile (lateLeakOpenedHistory G true secret).state = _
    rw [lateOpeningPublicKernel_move_law G profile (lateLeakOpenedHistory G true secret)
      (by change ¬False; exact not_false)]
    change ((profile .listener ((lateOpeningPublicModel G).infoOf .listener
      (lateLeakOpenedHistory G true secret).trace)).map Subtype.val).bind
        (lateLeakAdvance G (.answering secret .protectedOpen)) = _
    rw [lateOpeningPublic_listener_info_answering]
    change ((profile .listener (lateOpeningPublicListenerInfo secret.1 .protectedOpen)).map
      Subtype.val).bind (lateLeakAdvance G (.answering secret .protectedOpen)) = _
    rw [safe, PMF.pure_bind]
    simp [lateLeakAdvance, lateLeakReplyOf]
  have finished (secret : LateLeakType) (fuel : ℕ) :
      (fun law => law.bind (lateOpeningPublicKernel G profile))^[fuel]
        (PMF.pure (.finished secret .protectedOpen .safe)) =
          PMF.pure (.finished secret .protectedOpen .safe) := by
    induction fuel with
    | zero => rfl
    | succ fuel ih =>
      rw [Function.iterate_succ_apply, PMF.pure_bind,
        lateOpeningPublicKernel_terminal G profile (.finished secret .protectedOpen .safe)
          (by trivial), ih]
  rw [lateOpeningPublic_terminal_map_state, Function.iterate_succ_apply, PMF.pure_bind]
  change (fun law => law.bind (lateOpeningPublicKernel G profile))^[4]
    (lateOpeningPublicKernel G profile .initial) = _
  rw [lateOpeningPublicKernel_initial, ← PMF.bind_pure_comp, iterate_bind,
    lateLeakIntendedOutcome, ← PMF.bind_pure_comp]
  congr 1
  funext secret
  dsimp only [Function.comp_apply]
  rw [Function.iterate_succ_apply, PMF.pure_bind, protectedKernel,
    Function.iterate_succ_apply, PMF.pure_bind, answered, finished]

/-- In the strict failure-cost regime every native sequential equilibrium,
with arbitrary off-path beliefs, has the intended initialized state law. -/
theorem lateOpeningPublic_outcome_of_cost_gap (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (forfeit : 0 ≤ G.forfeit) (charge : 0 ≤ G.dropCharge)
    (gap : ∀ secret, lateOpeningPublicDeferralUpper G secret <
      lateOpeningPublicProtectedLower G secret)
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
      (lateLeak_terminates G true) (lateLeakPayoff G true)) :
    ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
      assessment.strategy (lateLeakExecution G true).initHistory).map
        ExecutionProtocol.History.state = lateLeakIntendedOutcome := by
  have opens (secret : LateLeakType) :
      ((assessment.strategy .sender) ((lateOpeningPublicModel G).infoOf .sender
        (lateLeakTypeHistory G true secret).trace)).map Subtype.val =
          PMF.pure (some (.opening true)) := by
    change (assessment.strategy .sender (lateOpeningPublicProtectedSenderSite G secret).1).map
      Subtype.val = _
    rw [lateOpeningPublic_rational_protected_pure G reward forfeit charge gap
      assessment equilibrium.1 secret, PMF.pure_map]
    rfl
  apply lateOpeningPublic_intended_outcome_of_protected_safe G assessment.strategy opens
  intro bit
  apply protected_rational_safe G assessment equilibrium.1 bit
  exact lateOpeningPublic_protected_bayes_label_uniform assessment
    (equilibrium.2.isBayesConsistent _) opens bit

/-- A fixed twice-reward forfeit and zero drop charge preserve the intended
state law at every content-blind inclusion probability strictly between zero
and one. In the high-probability regime the explicit public assessment is used;
in the low regime every equilibrium has the intended law. -/
theorem lateOpeningPublic_twice_reward_preserving_equilibrium (G : LateLeakParameters)
    (reward : 0 < G.reward) (forfeit : G.forfeit = 2 * G.reward) (charge : G.dropCharge = 0) :
    ∃ assessment : (lateOpeningPublicModel G).BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
        (lateLeak_terminates G true) (lateLeakPayoff G true) ∧
      ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
        assessment.strategy (lateLeakExecution G true).initHistory).map
          ExecutionProtocol.History.state = lateLeakIntendedOutcome := by
  classical
  by_cases high : 2 / 5 < lateLeakInclusionProb G
  · have margin : 0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
        G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge := by
      rw [forfeit, charge]
      nlinarith [mul_pos (sub_pos.mpr high) reward]
    have cost : G.reward / 2 < G.forfeit + G.dropCharge := by
      rw [forfeit, charge]
      linarith
    obtain ⟨assessment, equilibrium, canonical⟩ :=
      lateOpeningPublic_exists_sequential_equilibrium G reward.le cost margin
    refine ⟨assessment, equilibrium, ?_⟩
    rw [canonical, lateOpeningPublicCanonical_intended_outcome]
  · have low : lateLeakInclusionProb G < 3 / 4 := by linarith
    let fallback : ∀ who, (lateOpeningPublicModel G).Policy who :=
      fun _ _ => Classical.choice inferInstance
    obtain ⟨assessment, rational, consistent⟩ :=
      (lateOpeningPublicModel G).exists_sequentialEquilibrium
        (lateOpeningPublicModel_decisionRecall G) fallback (lateLeakPayoff G true)
        (lateLeak_terminates G true)
    have equilibrium : assessment.IsSequentialEquilibrium
        (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
        (lateLeak_terminates G true) (lateLeakPayoff G true) := ⟨rational, consistent⟩
    refine ⟨assessment, equilibrium, ?_⟩
    apply lateOpeningPublic_outcome_of_cost_gap G reward.le (by rw [forfeit]; positivity)
      (by simp [charge])
      (lateOpeningPublic_twice_reward_gap G reward forfeit charge low)
      assessment equilibrium

/-- At every inclusion probability, every original intended sequential
equilibrium has a full-public native equilibrium with the same complete state
law. The forfeit is intrinsic to this comparison game's failure utility. -/
theorem lateOpeningPublic_twice_reward_preserves_sequential_equilibria
    (G : LateLeakParameters) (reward : 0 < G.reward)
    (forfeit : G.forfeit = 2 * G.reward) (charge : G.dropCharge = 0)
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
  obtain ⟨target, targetEquilibrium, outcome⟩ :=
    lateOpeningPublic_twice_reward_preserving_equilibrium G reward forfeit charge
  exact ⟨target, targetEquilibrium,
    outcome.trans (lateLeak_intended_outcome source equilibrium).symm⟩

end Vegas
