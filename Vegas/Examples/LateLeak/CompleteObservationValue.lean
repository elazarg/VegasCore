/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.CompleteObservation
import GameTheory.Protocol.StateKernel

/-! # Actual continuation laws with complete public observation

The comparison game's state retains its entire execution path. Its public
information model includes own-action recall, but arbitrary behavioral profiles
still induce a state kernel: the unique retained trace reconstructs the exact
information argument. No private observation is pooled or erased.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

abbrev LateOpeningPublicProfile (G : LateLeakParameters) :=
  (who : LateLeakRole) → (lateOpeningPublicModel G).BehavioralPolicy who

open Classical in
/-- One step driven by the unique retained trace of a reached state. An
unreachable state and a terminal state are absorbed. -/
def lateOpeningPublicKernel (G : LateLeakParameters) (profile : LateOpeningPublicProfile G)
    (state : LateLeakState) : PMF LateLeakState :=
  if stopped : state.IsFinished then PMF.pure state
  else if reached : Nonempty ((lateLeakExecution G true).Trace state) then
    ((lateOpeningPublicModel G).behavioralJoint profile (Classical.choice reached) stopped).bind
      ((lateLeakExecution G true).step state)
  else PMF.pure state

theorem lateOpeningPublicKernel_terminal (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (state : LateLeakState)
    (stopped : state.IsFinished) :
    lateOpeningPublicKernel G profile state = PMF.pure state := by
  simp only [lateOpeningPublicKernel, dite_eq_left stopped]

/-- Reconstructed state execution uses the original history's exact private
information, since the protocol's retained trace is unique. -/
theorem lateOpeningPublicKernel_history (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (history : (lateLeakExecution G true).History)
    (running : ¬ history.state.IsFinished) :
    lateOpeningPublicKernel G profile history.state =
      ((lateOpeningPublicModel G).behavioralJoint profile history.trace running).bind
        ((lateLeakExecution G true).step history.state) := by
  have reached : Nonempty ((lateLeakExecution G true).Trace history.state) := ⟨history.trace⟩
  rw [lateOpeningPublicKernel, dite_eq_right running, dite_eq_left reached]
  have same : Classical.choice reached = history.trace :=
    (lateLeak_treeShaped G true history.state).allEq _ _
  rw [same]

/-- The state projection of native behavioral play is ordinary kernel
iteration, even for an arbitrary information-dependent replacement policy. -/
theorem lateOpeningPublic_run_map_state (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (fuel : ℕ)
    (history : (lateLeakExecution G true).History) :
    ((lateOpeningPublicModel G).runBehavioralFrom profile fuel history).map
      ExecutionProtocol.History.state =
      (fun law => law.bind (lateOpeningPublicKernel G profile))^[fuel]
        (PMF.pure history.state) := by
  unfold InformationModel.runBehavioralFrom
  apply ExecutionProtocol.runRandomizedFor_map_state
    ((lateOpeningPublicModel G).randomizedChooser profile)
  · exact fun state stopped => lateOpeningPublicKernel_terminal G profile state stopped
  · exact fun current running => (lateOpeningPublicKernel_history G profile current running).symm

theorem lateOpeningPublic_terminal_map_state (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G)
    (history : (lateLeakExecution G true).History) :
    ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
      profile history).map ExecutionProtocol.History.state =
      (fun law => law.bind (lateOpeningPublicKernel G profile))^[5]
        (PMF.pure history.state) := by
  rw [(lateOpeningPublicModel G).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (lateLeak_terminates G true) (lateLeak_bounded G true)]
  exact lateOpeningPublic_run_map_state G profile 5 history

/-- The native product draws only its active coordinate. -/
theorem lateOpeningPublicKernel_move_law (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (history : (lateLeakExecution G true).History)
    (running : ¬ history.state.IsFinished) :
    lateOpeningPublicKernel G profile history.state =
      ((profile history.state.mover
        ((lateOpeningPublicModel G).infoOf history.state.mover history.trace)).map Subtype.val).bind
        (lateLeakAdvance G history.state) := by
  rw [lateOpeningPublicKernel_history G profile history running]
  have unique : ∀ who, (lateLeakExecution G true).active history.state who →
      who = history.state.mover := by
    intro who acting
    change history.state.actor = some who at acting
    simp [LateLeakState.mover, acting]
  rw [(lateOpeningPublicModel G).behavioralJoint_eq_map_of_at_most_one_active profile history.trace
    running history.state.mover unique, PMF.bind_map, PMF.bind_map]
  congr 1
  funext choice
  change lateLeakAdvance G history.state
    ((lateLeakExecution G true).singletonJoint history.state.mover choice.1 history.state.mover) = _
  rw [ExecutionProtocol.singletonJoint_self]
  rfl

/-- The public reply after a resolved opening. -/
def lateOpeningPublicReply (secret : LateLeakType) (resolution : LateLeakResolution) :
    LateLeakAnswer :=
  if resolution.succeeded then .safe
  else .failure (if resolution = .withheld then false else secret.1)

/-- Every reached answering history materializes precisely the stated public
reply, including truthful replies to both late failed openings. -/
theorem lateOpeningPublicCanonical_answer_law (G : LateLeakParameters)
    (secret : LateLeakType) (resolution : LateLeakResolution)
    (trace : (lateLeakExecution G true).Trace (.answering secret resolution)) :
    ((lateOpeningPublicCanonical G .listener)
      ((lateOpeningPublicModel G).infoOf .listener trace)).map Subtype.val =
      PMF.pure (some (.reply (lateOpeningPublicReply secret resolution))) := by
  rw [lateOpeningPublic_listener_info_answering]
  cases resolution <;>
    simp [PMF.pure_map, lateOpeningPublicCanonical, lateOpeningPublicReply,
      lateOpeningPublicTranscript,
      lateLeakSignal, LateLeakSignal.success, LateLeakResolution.succeeded]

theorem lateOpeningPublicCanonical_opening_law (G : LateLeakParameters)
    (secret : LateLeakType) {state : LateLeakState}
    (trace : (lateLeakExecution G true).Trace state)
    (turn : state = .protectedTurn secret ∨ state = .secondLate secret) :
    ((lateOpeningPublicCanonical G .sender)
      ((lateOpeningPublicModel G).infoOf .sender trace)).map Subtype.val =
      PMF.pure (some (.opening true)) := by
  change ((lateOpeningPublicSenderPolicy G)
    (((lateOpeningPublicModel G).infoOf .sender trace).1.1)).map Subtype.val = _
  rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf]
  rcases turn with rfl | rfl <;>
    simp [PMF.pure_map, lateLeakView, lateOpeningPublicSenderPolicy]

/-- Safe-success and truthful-failure value of either late attempt. -/
def lateOpeningPublicAttemptValue (G : LateLeakParameters) (secret : LateLeakType) : ℝ :=
  lateLeakInclusionProb G * lateLeakSenderPayoff G secret .secondIncluded .safe +
    (1 - lateLeakInclusionProb G) *
      lateLeakSenderPayoff G secret .secondDropped (.failure secret.1)

/-- A payoff potential for every native continuation, including terminal
histories reached by arbitrary replacement policies. -/
def lateOpeningPublicSenderPotential (G : LateLeakParameters) : LateLeakState → ℝ
  | .initial | .protectedTurn _ => G.reward / 2
  | .firstLate secret | .secondLate secret => lateOpeningPublicAttemptValue G secret
  | .answering secret resolution =>
      lateLeakSenderPayoff G secret resolution (lateOpeningPublicReply secret resolution)
  | .finished secret resolution answer => lateLeakSenderPayoff G secret resolution answer

/-- The protected and late transmission primitives have exactly their stated
expected potentials, independently of any history-law approximation. -/
theorem lateOpeningPublic_transmission_potential (G : LateLeakParameters)
    (secret : LateLeakType) (state : LateLeakState)
    (turn : state = .protectedTurn secret ∨ state = .firstLate secret ∨
      state = .secondLate secret) :
    expect (lateLeakAdvance G state (some (.opening true)))
      (lateOpeningPublicSenderPotential G) =
      if state = .protectedTurn secret then G.reward / 2
      else lateOpeningPublicAttemptValue G secret := by
  rcases turn with rfl | rfl | rfl
  · simp [expect_pure, lateLeakAdvance, lateOpeningPublicSenderPotential, lateOpeningPublicReply,
      lateLeakSenderPayoff, lateLeakSenderBase, LateLeakResolution.succeeded,
      LateLeakResolution.droppedLate]
  · rw [lateLeakAdvance, ite_eq_left rfl, expect_map, lateLeak_expect_inclusion]
    simp [lateOpeningPublicSenderPotential, lateOpeningPublicReply,
      LateLeakResolution.succeeded, lateOpeningPublicAttemptValue,
      lateLeakSenderPayoff, lateLeakSenderBase, LateLeakResolution.droppedLate]
  · rw [lateLeakAdvance, ite_eq_left rfl, expect_map, lateLeak_expect_inclusion]
    simp [lateOpeningPublicSenderPotential, lateOpeningPublicReply,
      LateLeakResolution.succeeded, lateOpeningPublicAttemptValue]

/-- The canonical native response attains the sender potential at every
history. In particular, its first late mixture does not require pooling any
different private information values. -/
theorem lateOpeningPublic_canonical_step_value (G : LateLeakParameters)
    (history : (lateLeakExecution G true).History) :
    expect (lateOpeningPublicKernel G (lateOpeningPublicCanonical G) history.state)
      (lateOpeningPublicSenderPotential G) = lateOpeningPublicSenderPotential G history.state := by
  classical
  rcases history with ⟨state, trace⟩
  cases state with
  | finished secret resolution answer =>
      rw [lateOpeningPublicKernel_terminal _ _ _ (by trivial), expect_pure]
  | answering secret resolution =>
      rw [lateOpeningPublicKernel_move_law _ _ _ (by simp [LateLeakState.IsFinished])]
      change expect
        ((((lateOpeningPublicCanonical G .listener)
          ((lateOpeningPublicModel G).infoOf .listener trace)).map Subtype.val).bind
          (lateLeakAdvance G (.answering secret resolution))) _ = _
      rw [lateOpeningPublicCanonical_answer_law, PMF.pure_bind]
      simp [expect_pure, lateLeakAdvance, lateLeakReplyOf, lateOpeningPublicSenderPotential]
  | protectedTurn secret =>
      rw [lateOpeningPublicKernel_move_law _ _ _ (by simp [LateLeakState.IsFinished])]
      change expect
        ((((lateOpeningPublicCanonical G .sender)
          ((lateOpeningPublicModel G).infoOf .sender trace)).map Subtype.val).bind
          (lateLeakAdvance G (.protectedTurn secret))) _ = _
      rw [lateOpeningPublicCanonical_opening_law G secret trace (Or.inl rfl), PMF.pure_bind,
        lateOpeningPublic_transmission_potential G secret _ (Or.inl rfl)]
      simp [lateOpeningPublicSenderPotential]
  | secondLate secret =>
      rw [lateOpeningPublicKernel_move_law _ _ _ (by simp [LateLeakState.IsFinished])]
      change expect
        ((((lateOpeningPublicCanonical G .sender)
          ((lateOpeningPublicModel G).infoOf .sender trace)).map Subtype.val).bind
          (lateLeakAdvance G (.secondLate secret))) _ = _
      rw [lateOpeningPublicCanonical_opening_law G secret trace (Or.inr rfl), PMF.pure_bind,
        lateOpeningPublic_transmission_potential G secret _ (Or.inr (Or.inr rfl))]
      simp [lateOpeningPublicSenderPotential]
  | initial =>
      rw [lateOpeningPublicKernel_move_law _ _ _ (by simp [LateLeakState.IsFinished]),
        PMF.bind_map, expect_bind_of_finite]
      rw [← expect_constant _ (lateOpeningPublicSenderPotential G _)]
      apply expect_congr_on_support
      intro choice _supported
      dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
      have permitted := choice.2
      change choice.1 ∈ lateLeakMenu true
        (((lateOpeningPublicModel G).infoOf _ trace).1.1) at permitted
      rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf] at permitted
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_none, lateLeakView]
        at permitted
      have idle : choice.1 = none := permitted
      rw [idle]
      simp only [lateLeakAdvance, expect_map, lateOpeningPublicSenderPotential]
      exact expect_constant lateLeakPrior (G.reward / 2)
  | firstLate secret =>
      rw [lateOpeningPublicKernel_move_law _ _ _ (by simp [LateLeakState.IsFinished]),
        PMF.bind_map, expect_bind_of_finite]
      rw [← expect_constant _ (lateOpeningPublicSenderPotential G _)]
      apply expect_congr_on_support
      intro choice _supported
      dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
      have permitted := choice.2
      change choice.1 ∈ lateLeakMenu true
        (((lateOpeningPublicModel G).infoOf _ trace).1.1) at permitted
      rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf] at permitted
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, lateLeakView]
        at permitted
      obtain ⟨now, same⟩ := permitted
      rw [same]
      cases now
      · simp [expect_pure, lateLeakAdvance, lateOpeningPublicSenderPotential]
      · rw [lateOpeningPublic_transmission_potential G secret _ (Or.inr (Or.inl rfl))]
        simp [lateOpeningPublicSenderPotential]

/-- The actual native one-step law cannot increase the sender's payoff
potential when the opponent follows canonical public replies. -/
theorem lateOpeningPublic_sender_step_bound (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (cost : G.reward / 2 < G.forfeit + G.dropCharge)
    (margin : 0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
      G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge)
    (alternative : (lateOpeningPublicModel G).BehavioralPolicy .sender)
    (history : (lateLeakExecution G true).History) :
    expect (lateOpeningPublicKernel G
      (Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature)
        (lateOpeningPublicCanonical G) .sender alternative) history.state)
      (lateOpeningPublicSenderPotential G) ≤ lateOpeningPublicSenderPotential G history.state := by
  classical
  let profile : LateOpeningPublicProfile G :=
    Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature)
      (lateOpeningPublicCanonical G) .sender alternative
  change expect (lateOpeningPublicKernel G profile history.state) _ ≤ _
  rcases history with ⟨state, trace⟩
  cases state with
  | finished secret resolution answer =>
      rw [lateOpeningPublicKernel_terminal G profile _ (by trivial), expect_pure]
  | answering secret resolution =>
      rw [lateOpeningPublicKernel_move_law G profile _ (by simp [LateLeakState.IsFinished])]
      change expect
        (((profile .listener ((lateOpeningPublicModel G).infoOf .listener trace)).map
          Subtype.val).bind (lateLeakAdvance G (.answering secret resolution))) _ ≤ _
      rw [show profile .listener = lateOpeningPublicCanonical G .listener from
        Profile.update_of_ne _ _ (by decide), lateOpeningPublicCanonical_answer_law,
        PMF.pure_bind]
      simp [expect_pure, lateLeakAdvance, lateLeakReplyOf, lateOpeningPublicSenderPotential]
  | initial =>
      rw [lateOpeningPublicKernel_move_law G profile _ (by simp [LateLeakState.IsFinished]),
        PMF.bind_map, expect_bind_of_finite]
      apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
      intro choice _supported
      dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
      have permitted := choice.2
      change choice.1 ∈ lateLeakMenu true
        (((lateOpeningPublicModel G).infoOf _ trace).1.1) at permitted
      rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf] at permitted
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_none, lateLeakView]
        at permitted
      have idle : choice.1 = none := permitted
      rw [idle]
      simp only [lateLeakAdvance, expect_map, lateOpeningPublicSenderPotential]
      exact (expect_constant lateLeakPrior (G.reward / 2)).le
  | protectedTurn secret =>
      rw [lateOpeningPublicKernel_move_law G profile _ (by simp [LateLeakState.IsFinished]),
        PMF.bind_map, expect_bind_of_finite]
      apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
      intro choice _supported
      dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
      have permitted := choice.2
      change choice.1 ∈ lateLeakMenu true
        (((lateOpeningPublicModel G).infoOf _ trace).1.1) at permitted
      rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf] at permitted
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, lateLeakView]
        at permitted
      obtain ⟨now, same, _allowed⟩ := permitted
      rw [same]
      cases now
      · simpa [expect_pure, lateLeakAdvance, lateOpeningPublicSenderPotential,
            lateOpeningPublicAttemptValue, lateLeakSenderPayoff,
            lateLeakSenderBase, LateLeakResolution.succeeded,
            LateLeakResolution.droppedLate] using
          (lateOpeningPublic_protected_better G reward cost secret).le
      · rw [lateOpeningPublic_transmission_potential G secret _ (Or.inl rfl)]
        simp [lateOpeningPublicSenderPotential]
  | firstLate secret =>
      rw [lateOpeningPublicKernel_move_law G profile _ (by simp [LateLeakState.IsFinished]),
        PMF.bind_map, expect_bind_of_finite]
      apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
      intro choice _supported
      dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
      have permitted := choice.2
      change choice.1 ∈ lateLeakMenu true
        (((lateOpeningPublicModel G).infoOf _ trace).1.1) at permitted
      rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf] at permitted
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, lateLeakView]
        at permitted
      obtain ⟨now, same⟩ := permitted
      rw [same]
      cases now
      · simp [expect_pure, lateLeakAdvance, lateOpeningPublicSenderPotential]
      · rw [lateOpeningPublic_transmission_potential G secret _ (Or.inr (Or.inl rfl))]
        simp [lateOpeningPublicSenderPotential]
  | secondLate secret =>
      rw [lateOpeningPublicKernel_move_law G profile _ (by simp [LateLeakState.IsFinished]),
        PMF.bind_map, expect_bind_of_finite]
      apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
      intro choice _supported
      dsimp only [Function.comp_apply, ExecutionProtocol.History.state]
      have permitted := choice.2
      change choice.1 ∈ lateLeakMenu true
        (((lateOpeningPublicModel G).infoOf _ trace).1.1) at permitted
      rw [lateOpeningPublic_old_info_projection, lateLeak_infoOf] at permitted
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, lateLeakView]
        at permitted
      obtain ⟨now, same⟩ := permitted
      rw [same]
      cases now
      · simpa [expect_pure, lateLeakAdvance, lateOpeningPublicSenderPotential,
          lateOpeningPublicReply,
          LateLeakResolution.succeeded, lateOpeningPublicAttemptValue] using
          (lateOpeningPublic_last_send_better G reward margin secret).le
      · rw [lateOpeningPublic_transmission_potential G secret _ (Or.inr (Or.inr rfl))]
        simp [lateOpeningPublicSenderPotential]

/-- The one-step bound propagates through any number of actual adaptive
sender responses. The state kernel reconstructs every response's own recall. -/
theorem lateOpeningPublic_sender_iterate_bound (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (cost : G.reward / 2 < G.forfeit + G.dropCharge)
    (margin : 0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
      G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge)
    (alternative : (lateOpeningPublicModel G).BehavioralPolicy .sender)
    (fuel : ℕ) (state : LateLeakState) :
    expect ((fun law => law.bind (lateOpeningPublicKernel G
      (Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature)
        (lateOpeningPublicCanonical G) .sender alternative)))^[fuel] (PMF.pure state))
      (lateOpeningPublicSenderPotential G) ≤ lateOpeningPublicSenderPotential G state := by
  classical
  let profile : LateOpeningPublicProfile G :=
    Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature)
      (lateOpeningPublicCanonical G) .sender alternative
  have one (current : LateLeakState) :
      expect (lateOpeningPublicKernel G profile current)
        (lateOpeningPublicSenderPotential G) ≤ lateOpeningPublicSenderPotential G current := by
    by_cases reached : Nonempty ((lateLeakExecution G true).Trace current)
    · exact lateOpeningPublic_sender_step_bound G reward cost margin alternative
        ⟨current, Classical.choice reached⟩
    · by_cases stopped : current.IsFinished
      · simp [lateOpeningPublicKernel, stopped, expect_pure]
      · simp [lateOpeningPublicKernel, stopped, reached, expect_pure]
  change expect ((fun law => law.bind (lateOpeningPublicKernel G profile))^[fuel]
    (PMF.pure state)) _ ≤ _
  induction fuel with
  | zero => simp [expect_pure]
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', expect_bind_of_finite]
      exact (expect_mono (fun current _ => one current) (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _)).trans ih

/-- Terminal payoffs agree with the sender potential under every profile. -/
theorem lateOpeningPublic_terminal_potential_eq (G : LateLeakParameters)
    (profile : LateOpeningPublicProfile G) (history : (lateLeakExecution G true).History) :
    expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom
      (lateLeak_terminates G true) profile history) (lateLeakPayoff G true .sender) =
      expect (((lateOpeningPublicModel G).runBehavioralTerminalFrom
        (lateLeak_terminates G true) profile history).map ExecutionProtocol.History.state)
        (lateOpeningPublicSenderPotential G) := by
  rw [expect_map]
  apply expect_congr_on_support
  intro final supported
  have stopped := (lateOpeningPublicModel G).runBehavioralTerminalFrom_support_terminal
    (lateLeak_terminates G true) profile history final supported
  rcases final with ⟨state, trace⟩
  cases state with
  | finished secret resolution answer => rfl
  | _ => exact stopped.elim

/-- Canonical terminal play attains its payoff potential from every retained
history, including information sets with zero initialized probability. -/
theorem lateOpeningPublic_canonical_continuation_value (G : LateLeakParameters)
    (history : (lateLeakExecution G true).History) :
    expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom
      (lateLeak_terminates G true) (lateOpeningPublicCanonical G) history)
      (lateLeakPayoff G true .sender) = lateOpeningPublicSenderPotential G history.state := by
  classical
  have one (state : LateLeakState) :
      expect (lateOpeningPublicKernel G (lateOpeningPublicCanonical G) state)
        (lateOpeningPublicSenderPotential G) = lateOpeningPublicSenderPotential G state := by
    by_cases reached : Nonempty ((lateLeakExecution G true).Trace state)
    · exact lateOpeningPublic_canonical_step_value G ⟨state, Classical.choice reached⟩
    · by_cases stopped : state.IsFinished
      · simp [lateOpeningPublicKernel, stopped, expect_pure]
      · simp [lateOpeningPublicKernel, stopped, reached, expect_pure]
  have iterates (fuel : ℕ) :
      expect ((fun law => law.bind (lateOpeningPublicKernel G
        (lateOpeningPublicCanonical G)))^[fuel] (PMF.pure history.state))
        (lateOpeningPublicSenderPotential G) =
          lateOpeningPublicSenderPotential G history.state := by
    induction fuel with
    | zero => simp [expect_pure]
    | succ fuel ih =>
        rw [Function.iterate_succ_apply', expect_bind_of_finite]
        calc
          _ = expect _ (lateOpeningPublicSenderPotential G) :=
            expect_congr_on_support (fun state _ => one state)
          _ = _ := ih
  rw [lateOpeningPublic_terminal_potential_eq, lateOpeningPublic_terminal_map_state]
  exact iterates 5

/-- Every whole information-dependent sender deviation is bounded by the
same initial potential under the canonical opponent's actual public replies. -/
theorem lateOpeningPublic_sender_continuation_bound (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (cost : G.reward / 2 < G.forfeit + G.dropCharge)
    (margin : 0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
      G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge)
    (alternative : (lateOpeningPublicModel G).BehavioralPolicy .sender)
    (history : (lateLeakExecution G true).History) :
    expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom (lateLeak_terminates G true)
      (Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature)
        (lateOpeningPublicCanonical G) .sender alternative) history)
      (lateLeakPayoff G true .sender) ≤ lateOpeningPublicSenderPotential G history.state := by
  let profile : LateOpeningPublicProfile G :=
    Profile.update (sig := (lateOpeningPublicModel G).behavioralSignature)
      (lateOpeningPublicCanonical G) .sender alternative
  change expect ((lateOpeningPublicModel G).runBehavioralTerminalFrom _ profile history) _ ≤ _
  rw [lateOpeningPublic_terminal_potential_eq, lateOpeningPublic_terminal_map_state]
  exact lateOpeningPublic_sender_iterate_bound G reward cost margin alternative 5 history.state

/-- The sender's whole-policy best response holds under any history beliefs
when the assessment plays the constructed canonical strategy. -/
theorem lateOpeningPublic_sender_context_best_response (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (cost : G.reward / 2 < G.forfeit + G.dropCharge)
    (margin : 0 < lateLeakInclusionProb G * (G.forfeit + G.reward / 2) -
      G.reward - (1 - lateLeakInclusionProb G) * G.dropCharge)
    (assessment : (lateOpeningPublicModel G).BehavioralAssessment)
    (canonical : assessment.strategy = lateOpeningPublicCanonical G)
    (site : (lateOpeningPublicModel G).InformationSite .sender)
    (alternative : (lateOpeningPublicModel G).BehavioralPolicy .sender) :
    (assessment.continuationContext (lateLeak_terminates G true) site
      (lateLeakPayoff G true .sender)).value alternative ≤
    (assessment.continuationContext (lateLeak_terminates G true) site
      (lateLeakPayoff G true .sender)).value (assessment.strategy .sender) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value,
    expect_bind_of_finite, expect_bind_of_finite, canonical]
  simp only [Profile.update_eq_self]
  apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  intro history _supported
  exact (lateOpeningPublic_sender_continuation_bound G reward cost margin alternative
    history.1).trans_eq
    (lateOpeningPublic_canonical_continuation_value G history.1).symm

end Vegas
