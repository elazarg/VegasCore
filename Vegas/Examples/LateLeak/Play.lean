/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Game
import GameTheory.Protocol.StateKernel
import GameTheoryExtensions.Analysis.Protocol.ContinuationDecision
import GameTheoryExtensions.Analysis.Protocol.ReachBounds

/-! # Play of the late-turn game

Information states are functions of execution states, so behavioral play of
the late-turn game forgets its history: the state law of play is the iterated
state kernel of the profile. Continuation values, reach weights and the
listener's decision problem at each of its information sets are computed from
that kernel.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {G : LateLeakParameters} {late : Bool}

/-- A behavioral profile of the late-turn game. -/
abbrev LateLeakProfile (G : LateLeakParameters) (late : Bool) : Type :=
  (who : LateLeakRole) → (lateLeakModel G late).BehavioralPolicy who

/-- Replace one player's policy in a profile. -/
abbrev lateLeakUpdate (profile : LateLeakProfile G late) (who : LateLeakRole)
    (policy : (lateLeakModel G late).BehavioralPolicy who) : LateLeakProfile G late :=
  Profile.update (sig := (lateLeakModel G late).behavioralSignature) profile who policy

theorem lateLeakUpdate_self (profile : LateLeakProfile G late) (who : LateLeakRole) :
    lateLeakUpdate profile who (profile who) = profile :=
  Profile.update_eq_self _ _

theorem lateLeak_model_infoOf (G : LateLeakParameters) (late : Bool) (who : LateLeakRole)
    {state : LateLeakState}
    (trace : (lateLeakExecution G late).Trace state) :
    (lateLeakModel G late).infoOf who trace = lateLeakView who state :=
  lateLeak_infoOf G late who trace

/-! ## The state kernel -/

/-- The mover's law over its own options at a state. -/
def lateLeakMoveLaw (profile : LateLeakProfile G late) (state : LateLeakState) :
    PMF (Option LateLeakMove) :=
  (profile state.mover (lateLeakView state.mover state)).map Subtype.val

/-- One step of play from a state. -/
def lateLeakKernel (profile : LateLeakProfile G late) (state : LateLeakState) :
    PMF LateLeakState :=
  (lateLeakMoveLaw profile state).bind (lateLeakAdvance G state)

/-- One step of play from a law over states. -/
def lateLeakFlow (profile : LateLeakProfile G late) (law : PMF LateLeakState) :
    PMF LateLeakState :=
  law.bind (lateLeakKernel profile)

theorem lateLeakFlow_apply (profile : LateLeakProfile G late) (law : PMF LateLeakState) :
    lateLeakFlow profile law = law.bind (lateLeakKernel profile) := rfl

theorem lateLeakFlow_pure (profile : LateLeakProfile G late) (state : LateLeakState) :
    lateLeakFlow profile (PMF.pure state) = lateLeakKernel profile state :=
  PMF.pure_bind _ _

/-- The behavioral joint law followed by the transition is the state kernel. -/
theorem lateLeak_joint_bind_step (profile : LateLeakProfile G late)
    (history : (lateLeakExecution G late).History)
    (running : ¬ (lateLeakExecution G late).terminal history.state) :
    ((lateLeakModel G late).behavioralJoint profile history.trace running).bind
      ((lateLeakExecution G late).step history.state) = lateLeakKernel profile history.state := by
  have unique : ∀ who, (lateLeakExecution G late).active history.state who →
      who = history.state.mover := by
    intro who acting
    change history.state.actor = some who at acting
    simp [LateLeakState.mover, acting]
  rw [(lateLeakModel G late).behavioralJoint_eq_map_of_at_most_one_active profile history.trace
    running history.state.mover unique, PMF.bind_map]
  calc _ = (profile history.state.mover
        ((lateLeakModel G late).infoOf history.state.mover history.trace)).bind
        (fun choice => lateLeakAdvance G history.state choice.1) := by
        congr 1
        funext choice
        simp only [Function.comp_apply]
        change lateLeakAdvance G history.state
          ((lateLeakExecution G late).singletonJoint history.state.mover choice.1
            history.state.mover) = _
        rw [ExecutionProtocol.singletonJoint_self]
    _ = _ := by
        rw [lateLeak_model_infoOf, lateLeakKernel, lateLeakMoveLaw, PMF.bind_map]
        rfl

theorem lateLeakKernel_finished (profile : LateLeakProfile G late) (secret : LateLeakType)
    (resolution : LateLeakResolution) (answer : LateLeakAnswer) :
    lateLeakKernel profile (.finished secret resolution answer) =
      PMF.pure (.finished secret resolution answer) := by
  change (lateLeakMoveLaw profile _).bind (fun _ => PMF.pure _) = _
  exact PMF.bind_const _ _

/-- The state law of behavioral play is the iterated state kernel. -/
theorem lateLeak_run_map_state (profile : LateLeakProfile G late) (fuel : ℕ)
    (history : (lateLeakExecution G late).History) :
    ((lateLeakModel G late).runBehavioralFrom profile fuel history).map
        ExecutionProtocol.History.state =
      (lateLeakFlow profile)^[fuel] (PMF.pure history.state) := by
  unfold lateLeakFlow InformationModel.runBehavioralFrom
  exact ExecutionProtocol.runRandomizedFor_map_state
    ((lateLeakModel G late).randomizedChooser profile) (lateLeakKernel profile)
    (fun state stopped => by
      cases state with
      | finished secret resolution answer => exact lateLeakKernel_finished profile _ _ _
      | _ => exact stopped.elim)
    (fun history running => lateLeak_joint_bind_step profile history running) fuel history

/-- Terminal play has the five-step state law. -/
theorem lateLeak_terminal_map_state (certificate : (lateLeakExecution G late).WellFoundedHistories)
    (profile : LateLeakProfile G late) (history : (lateLeakExecution G late).History) :
    ((lateLeakModel G late).runBehavioralTerminalFrom certificate profile history).map
        ExecutionProtocol.History.state =
      (lateLeakFlow profile)^[5] (PMF.pure history.state) := by
  rw [(lateLeakModel G late).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
    (lateLeak_bounded G late)]
  exact lateLeak_run_map_state profile 5 history

theorem lateLeakFlow_iterate_eq_bind (profile : LateLeakProfile G late) (fuel : ℕ)
    (law : PMF LateLeakState) :
    (lateLeakFlow profile)^[fuel] law =
      law.bind fun state => (lateLeakFlow profile)^[fuel] (PMF.pure state) := by
  induction fuel generalizing law with
  | zero => simp only [Function.iterate_zero_apply, PMF.bind_pure]
  | succ fuel ih =>
      rw [Function.iterate_succ_apply, ih, lateLeakFlow_apply, PMF.bind_bind]
      congr 1
      funext state
      rw [Function.iterate_succ_apply, lateLeakFlow_pure, ih]

/-! ## Values -/

/-- The expected payoff of play from a state after `fuel` steps. -/
def lateLeakValue (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ) (fuel : ℕ)
    (state : LateLeakState) : ℝ :=
  expect ((lateLeakFlow profile)^[fuel] (PMF.pure state)) payoff

theorem lateLeakValue_succ (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (fuel : ℕ) (state : LateLeakState) :
    lateLeakValue profile payoff (fuel + 1) state =
      expect (lateLeakKernel profile state) (lateLeakValue profile payoff fuel) := by
  unfold lateLeakValue
  rw [Function.iterate_succ_apply, lateLeakFlow_pure, lateLeakFlow_iterate_eq_bind,
    expect_bind_of_finite]

theorem lateLeakValue_finished (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (fuel : ℕ) (secret : LateLeakType) (resolution : LateLeakResolution)
    (answer : LateLeakAnswer) :
    lateLeakValue profile payoff fuel (.finished secret resolution answer) =
      payoff (.finished secret resolution answer) := by
  induction fuel with
  | zero => simp only [lateLeakValue, Function.iterate_zero_apply, expect_pure]
  | succ fuel ih => rw [lateLeakValue_succ, lateLeakKernel_finished, expect_pure, ih]

/-- The sender's law over its options at one of its states. -/
def lateLeakOpeningLaw (profile : LateLeakProfile G late) (state : LateLeakState) :
    PMF (Option LateLeakMove) :=
  (profile .sender (.full state)).map Subtype.val

/-- The listener's law over its options after a signal. -/
def lateLeakReplyLaw (profile : LateLeakProfile G late) (signal : LateLeakSignal) :
    PMF (Option LateLeakMove) :=
  (profile .listener (.asked signal)).map Subtype.val

/-- The probability that the sender opens now at a state. -/
def lateLeakOpenProb (profile : LateLeakProfile G late) (state : LateLeakState) : ℝ :=
  (lateLeakOpeningLaw profile state (some (.opening true))).toReal

/-- The probability of the safe answer after a signal. -/
def lateLeakSafeProb (profile : LateLeakProfile G late) (signal : LateLeakSignal) : ℝ :=
  (lateLeakReplyLaw profile signal (some (.reply .safe))).toReal

/-- The probability of the bit guess `1` after a signal. -/
def lateLeakBitOneProb (profile : LateLeakProfile G late) (signal : LateLeakSignal) : ℝ :=
  (lateLeakReplyLaw profile signal (some (.reply (.failure true)))).toReal

theorem lateLeakInclusion_true : (lateLeakInclusion G true).toReal = lateLeakInclusionProb G := by
  simp only [lateLeakInclusion, PMF.ofFintype_apply, ite_true]
  exact ENNReal.toReal_ofReal (lateLeakInclusionProb_pos G).le

theorem lateLeakInclusion_false :
    (lateLeakInclusion G false).toReal = 1 - lateLeakInclusionProb G := by
  simp only [lateLeakInclusion, PMF.ofFintype_apply, Bool.false_eq_true, ite_false]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (lateLeakInclusionProb_lt_one G).le)

theorem lateLeakInclusion_ne_zero (included : Bool) : lateLeakInclusion G included ≠ 0 := by
  have q0 := lateLeakInclusionProb_pos G
  have q1 := lateLeakInclusionProb_lt_one G
  cases included <;> simp [lateLeakInclusion, PMF.ofFintype_apply, q0, q1]

theorem lateLeakPrior_ne_zero (secret : LateLeakType) : lateLeakPrior secret ≠ 0 := by
  simp only [lateLeakPrior, PMF.ofFintype_apply, ne_eq, ENNReal.coe_eq_zero]
  split <;> norm_num

/-- A law that pays `y` away from one point. -/
theorem lateLeak_expect_two_point {α : Type*} [Finite α] (μ : PMF α) (a : α)
    (g : α → ℝ) (y : ℝ) (off : ∀ x ∈ μ.support, x ≠ a → g x = y) :
    expect μ g = (μ a).toReal * g a + (1 - (μ a).toReal) * y := by
  classical
  have := Fintype.ofFinite α
  have total : ∑ x, (μ x).toReal = 1 := by
    have weights := expect_eq_sum μ (fun _ => (1 : ℝ))
    rw [expect_constant] at weights
    simpa using weights.symm
  have pointwise : ∀ x, (μ x).toReal * g x =
      (μ x).toReal * y + (if x = a then (μ a).toReal * (g a - y) else 0) := by
    intro x
    by_cases same : x = a
    · subst same
      simp only [ite_true]
      ring
    · by_cases supported : x ∈ μ.support
      · simp [same, off x supported same]
      · have zero : μ x = 0 := (PMF.apply_eq_zero_iff μ x).mpr supported
        simp [same, zero]
  rw [expect_eq_sum, Finset.sum_congr rfl fun x _ => pointwise x, Finset.sum_add_distrib,
    ← Finset.sum_mul, total, Finset.sum_ite_eq' Finset.univ a]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem lateLeak_expect_inclusion (g : Bool → ℝ) :
    expect (lateLeakInclusion G) g =
      lateLeakInclusionProb G * g true + (1 - lateLeakInclusionProb G) * g false := by
  rw [expect_eq_sum, Fintype.sum_bool, lateLeakInclusion_true, lateLeakInclusion_false]

/-- The value of an answering state. -/
def lateLeakAnswerValue (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (secret : LateLeakType) (resolution : LateLeakResolution) : ℝ :=
  expect (lateLeakReplyLaw profile (lateLeakSignal secret resolution))
    fun choice => payoff (.finished secret resolution (lateLeakReplyOf choice))

/-- The value of sending a late opening. -/
def lateLeakSendValue (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (secret : LateLeakType) (included dropped : LateLeakResolution) : ℝ :=
  lateLeakInclusionProb G * lateLeakAnswerValue profile payoff secret included +
    (1 - lateLeakInclusionProb G) * lateLeakAnswerValue profile payoff secret dropped

/-- The value at the second late turn. -/
def lateLeakSecondValue (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (secret : LateLeakType) : ℝ :=
  lateLeakOpenProb profile (.secondLate secret) *
      lateLeakSendValue profile payoff secret .secondIncluded .secondDropped +
    (1 - lateLeakOpenProb profile (.secondLate secret)) *
      lateLeakAnswerValue profile payoff secret .withheld

/-- The value at the first late turn. -/
def lateLeakFirstValue (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (secret : LateLeakType) : ℝ :=
  lateLeakOpenProb profile (.firstLate secret) *
      lateLeakSendValue profile payoff secret .firstIncluded .firstDropped +
    (1 - lateLeakOpenProb profile (.firstLate secret)) *
      lateLeakSecondValue profile payoff secret

/-- The value at the protected turn. -/
def lateLeakProtectedValue (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (secret : LateLeakType) : ℝ :=
  lateLeakOpenProb profile (.protectedTurn secret) *
      lateLeakAnswerValue profile payoff secret .protectedOpen +
    (1 - lateLeakOpenProb profile (.protectedTurn secret)) *
      lateLeakFirstValue profile payoff secret

theorem lateLeakValue_answering (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (fuel : ℕ) (secret : LateLeakType) (resolution : LateLeakResolution) :
    lateLeakValue profile payoff (fuel + 1) (.answering secret resolution) =
      lateLeakAnswerValue profile payoff secret resolution := by
  rw [lateLeakValue_succ]
  change expect ((lateLeakReplyLaw profile (lateLeakSignal secret resolution)).bind
    (lateLeakAdvance G (.answering secret resolution))) _ = _
  rw [expect_bind_of_finite]
  simp only [lateLeakAdvance, expect_pure, lateLeakValue_finished, lateLeakAnswerValue]

private theorem value_send (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (fuel : ℕ) (secret : LateLeakType) (included dropped : LateLeakResolution) :
    expect ((lateLeakInclusion G).map fun inclusion =>
        LateLeakState.answering secret (if inclusion then included else dropped))
      (lateLeakValue profile payoff (fuel + 1)) =
      lateLeakSendValue profile payoff secret included dropped := by
  rw [expect_map, lateLeak_expect_inclusion]
  simp only [Function.comp_apply, ite_true, Bool.false_eq_true, ite_false,
    lateLeakValue_answering, lateLeakSendValue]

theorem lateLeakValue_secondLate (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (fuel : ℕ) (secret : LateLeakType) :
    lateLeakValue profile payoff (fuel + 2) (.secondLate secret) =
      lateLeakSecondValue profile payoff secret := by
  rw [lateLeakValue_succ]
  change expect ((lateLeakOpeningLaw profile (.secondLate secret)).bind
    (lateLeakAdvance G (.secondLate secret))) _ = _
  rw [expect_bind_of_finite, lateLeak_expect_two_point _ (some (.opening true)) _
    (lateLeakAnswerValue profile payoff secret .withheld)]
  · simp only [lateLeakAdvance, ite_true, value_send, lateLeakSecondValue, lateLeakOpenProb]
  · intro choice _ different
    simp only [lateLeakAdvance, different, ite_false, expect_pure, lateLeakValue_answering]

theorem lateLeakValue_firstLate (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (fuel : ℕ) (secret : LateLeakType) :
    lateLeakValue profile payoff (fuel + 3) (.firstLate secret) =
      lateLeakFirstValue profile payoff secret := by
  rw [lateLeakValue_succ]
  change expect ((lateLeakOpeningLaw profile (.firstLate secret)).bind
    (lateLeakAdvance G (.firstLate secret))) _ = _
  rw [expect_bind_of_finite, lateLeak_expect_two_point _ (some (.opening true)) _
    (lateLeakSecondValue profile payoff secret)]
  · simp only [lateLeakAdvance, ite_true, value_send, lateLeakFirstValue, lateLeakOpenProb]
  · intro choice _ different
    simp only [lateLeakAdvance, different, ite_false, expect_pure, lateLeakValue_secondLate]

theorem lateLeakValue_protectedTurn (profile : LateLeakProfile G late)
    (payoff : LateLeakState → ℝ) (fuel : ℕ) (secret : LateLeakType) :
    lateLeakValue profile payoff (fuel + 4) (.protectedTurn secret) =
      lateLeakProtectedValue profile payoff secret := by
  rw [lateLeakValue_succ]
  change expect ((lateLeakOpeningLaw profile (.protectedTurn secret)).bind
    (lateLeakAdvance G (.protectedTurn secret))) _ = _
  rw [expect_bind_of_finite, lateLeak_expect_two_point _ (some (.opening true)) _
    (lateLeakFirstValue profile payoff secret)]
  · simp only [lateLeakAdvance, ite_true, expect_pure, lateLeakValue_answering,
      lateLeakProtectedValue, lateLeakOpenProb]
  · intro choice _ different
    simp only [lateLeakAdvance, different, ite_false, expect_pure, lateLeakValue_firstLate]

theorem lateLeakValue_initial (profile : LateLeakProfile G late) (payoff : LateLeakState → ℝ)
    (fuel : ℕ) :
    lateLeakValue profile payoff (fuel + 5) .initial =
      expect lateLeakPrior fun secret => lateLeakProtectedValue profile payoff secret := by
  rw [lateLeakValue_succ]
  change expect ((lateLeakMoveLaw profile .initial).bind
    fun _ => lateLeakPrior.map LateLeakState.protectedTurn) _ = _
  rw [PMF.bind_const, expect_map]
  simp only [Function.comp_def, lateLeakValue_protectedTurn]

/-! ## Updating one player -/

theorem lateLeakReplyLaw_update_sender (profile : LateLeakProfile G late)
    (policy : (lateLeakModel G late).BehavioralPolicy .sender) (signal : LateLeakSignal) :
    lateLeakReplyLaw (lateLeakUpdate profile .sender policy) signal =
      lateLeakReplyLaw profile signal := by
  simp only [lateLeakReplyLaw, lateLeakUpdate, Profile.update_of_ne _ _ (by decide :
    LateLeakRole.listener ≠ LateLeakRole.sender)]

theorem lateLeakAnswerValue_update_sender (profile : LateLeakProfile G late)
    (policy : (lateLeakModel G late).BehavioralPolicy .sender) (payoff : LateLeakState → ℝ)
    (secret : LateLeakType) (resolution : LateLeakResolution) :
    lateLeakAnswerValue (lateLeakUpdate profile .sender policy) payoff secret resolution =
      lateLeakAnswerValue profile payoff secret resolution := by
  simp only [lateLeakAnswerValue, lateLeakReplyLaw_update_sender]

theorem lateLeakSendValue_update_sender (profile : LateLeakProfile G late)
    (policy : (lateLeakModel G late).BehavioralPolicy .sender) (payoff : LateLeakState → ℝ)
    (secret : LateLeakType) (included dropped : LateLeakResolution) :
    lateLeakSendValue (lateLeakUpdate profile .sender policy) payoff secret included dropped =
      lateLeakSendValue profile payoff secret included dropped := by
  simp only [lateLeakSendValue, lateLeakAnswerValue_update_sender]

theorem lateLeakOpeningLaw_update_sender (profile : LateLeakProfile G late)
    (policy : (lateLeakModel G late).BehavioralPolicy .sender) (state : LateLeakState) :
    lateLeakOpeningLaw (lateLeakUpdate profile .sender policy) state =
      (policy (.full state)).map Subtype.val := by
  simp only [lateLeakOpeningLaw, lateLeakUpdate, Profile.update_same]

/-- The sender's option to open now, or not, at one of its states. -/
def lateLeakOpenChoice (G : LateLeakParameters) (late : Bool) (state : LateLeakState) (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu late (.full state)) :
    (lateLeakModel G late).Choice .sender (.full state) :=
  ⟨some (.opening now), allowed⟩

/-- Commit the sender to one option at one of its states. -/
def lateLeakCommitOpen (policy : (lateLeakModel G late).BehavioralPolicy .sender)
    (state : LateLeakState) (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu late (.full state)) :
    (lateLeakModel G late).BehavioralPolicy .sender :=
  policy.commit (.full state) (lateLeakOpenChoice G late state now allowed)

theorem lateLeakCommitOpen_self (policy : (lateLeakModel G late).BehavioralPolicy .sender)
    (state : LateLeakState) (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu late (.full state)) :
    ((lateLeakCommitOpen policy state now allowed) (.full state)).map Subtype.val =
      PMF.pure (some (.opening now)) := by
  rw [lateLeakCommitOpen,
    InformationModel.BehavioralPolicy.commit_self (M := lateLeakModel G late), PMF.pure_map]
  rfl

theorem lateLeakCommitOpen_of_ne (policy : (lateLeakModel G late).BehavioralPolicy .sender)
    (state other : LateLeakState) (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu late (.full state))
    (different : other ≠ state) :
    (lateLeakCommitOpen policy state now allowed) (.full other) = policy (.full other) := by
  rw [lateLeakCommitOpen,
    InformationModel.BehavioralPolicy.commit_of_ne (M := lateLeakModel G late)]
  intro same
  exact different (LateLeakView.full.inj same)

/-! ## Reach weights -/

/-- The reach weight of a history is that of its predecessor times one kernel
step. -/
theorem lateLeak_reachWeight_step (profile : LateLeakProfile G late)
    (history : (lateLeakExecution G late).History) (positive : 0 < history.trace.length) :
    (lateLeakModel G late).historyReachWeight profile history =
      (lateLeakModel G late).historyReachWeight profile history.prior *
        lateLeakKernel profile history.prior.state history.state := by
  rw [(lateLeakModel G late).historyReachWeight_eq_prior_mul profile history positive]
  congr 1
  have mapped := lateLeak_run_map_state profile 1 history.prior
  have injective := pmf_map_apply_of_injective
    ((lateLeakModel G late).runBehavioralFrom profile 1 history.prior)
    (lateLeak_state_injective G late) history
  rw [← injective]
  change (PMF.map ExecutionProtocol.History.state
    ((lateLeakModel G late).runBehavioralFrom profile 1 history.prior)) history.state = _
  rw [mapped, Function.iterate_one, lateLeakFlow_pure]

theorem lateLeak_reachWeight_init (profile : LateLeakProfile G late) :
    (lateLeakModel G late).historyReachWeight profile (lateLeakExecution G late).initHistory = 1 :=
  (lateLeakModel G late).historyReachWeight_initHistory profile

/-- The kernel mass of one target is the mover's mass at the move leading
there, times the transition mass. -/
theorem lateLeakKernel_apply (profile : LateLeakProfile G late) (state target : LateLeakState) :
    lateLeakKernel profile state target =
      ∑' choice, lateLeakMoveLaw profile state choice * lateLeakAdvance G state choice target :=
  PMF.bind_apply _ _ _

theorem lateLeakKernel_initial (profile : LateLeakProfile G late) (secret : LateLeakType) :
    lateLeakKernel profile .initial (.protectedTurn secret) = lateLeakPrior secret := by
  change ((lateLeakMoveLaw profile .initial).bind
    fun _ => lateLeakPrior.map LateLeakState.protectedTurn) _ = _
  rw [PMF.bind_const]
  exact pmf_map_apply_of_injective _ (fun _ _ same => LateLeakState.protectedTurn.inj same) _

/-- Every option of the sender at one of its states is to open now or not. -/
theorem lateLeakOpeningLaw_support (profile : LateLeakProfile G late) (state : LateLeakState)
    (acting : state.actor = some .sender) (choice : Option LateLeakMove)
    (supported : choice ∈ (lateLeakOpeningLaw profile state).support) :
    ∃ now, choice = some (.opening now) := by
  rw [lateLeakOpeningLaw, PMF.mem_support_map_iff] at supported
  obtain ⟨option, _, rfl⟩ := supported
  have menu := option.2
  change option.1 ∈ lateLeakMenu late (.full state) at menu
  cases state with
  | protectedTurn secret =>
      obtain ⟨now, same, -⟩ := menu
      exact ⟨now, same⟩
  | firstLate secret => exact menu
  | secondLate secret => exact menu
  | _ => simp [LateLeakState.actor] at acting

private theorem kernel_sender_apply (profile : LateLeakProfile G late)
    (state target : LateLeakState)
    (acting : state.actor = some .sender) (now : Bool)
    (only : ∀ other, other ≠ now → lateLeakAdvance G state (some (.opening other)) target = 0) :
    lateLeakKernel profile state target =
      lateLeakOpeningLaw profile state (some (.opening now)) *
        lateLeakAdvance G state (some (.opening now)) target := by
  rw [lateLeakKernel_apply]
  have law : lateLeakMoveLaw profile state = lateLeakOpeningLaw profile state := by
    have mover : state.mover = .sender := by simp [LateLeakState.mover, acting]
    unfold lateLeakMoveLaw lateLeakOpeningLaw
    rw [mover]
    rfl
  rw [law, tsum_eq_single (some (LateLeakMove.opening now))]
  intro choice different
  by_cases supported : choice ∈ (lateLeakOpeningLaw profile state).support
  · obtain ⟨other, rfl⟩ := lateLeakOpeningLaw_support profile state acting choice supported
    have : other ≠ now := fun same => different (by rw [same])
    rw [only other this, mul_zero]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul]

theorem lateLeakKernel_protected_open (profile : LateLeakProfile G late) (secret : LateLeakType) :
    lateLeakKernel profile (.protectedTurn secret) (.answering secret .protectedOpen) =
      lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening true)) := by
  rw [kernel_sender_apply profile _ _ rfl true]
  · simp [lateLeakAdvance]
  · intro other different
    cases other
    · simp [lateLeakAdvance]
    · exact (different rfl).elim

theorem lateLeakKernel_protected_wait (profile : LateLeakProfile G late) (secret : LateLeakType) :
    lateLeakKernel profile (.protectedTurn secret) (.firstLate secret) =
      lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) := by
  rw [kernel_sender_apply profile _ _ rfl false]
  · simp [lateLeakAdvance]
  · intro other different
    cases other
    · exact (different rfl).elim
    · simp [lateLeakAdvance]

theorem lateLeakKernel_first_hold (profile : LateLeakProfile G late) (secret : LateLeakType) :
    lateLeakKernel profile (.firstLate secret) (.secondLate secret) =
      lateLeakOpeningLaw profile (.firstLate secret) (some (.opening false)) := by
  rw [kernel_sender_apply profile _ _ rfl false]
  · simp [lateLeakAdvance]
  · intro other different
    cases other
    · exact (different rfl).elim
    · simp [lateLeakAdvance, PMF.map_apply]

theorem lateLeakKernel_first_send (profile : LateLeakProfile G late) (secret : LateLeakType)
    (included : Bool) :
    lateLeakKernel profile (.firstLate secret)
        (.answering secret (if included then .firstIncluded else .firstDropped)) =
      lateLeakOpeningLaw profile (.firstLate secret) (some (.opening true)) *
        lateLeakInclusion G included := by
  rw [kernel_sender_apply profile _ _ rfl true]
  · congr 1
    simp only [lateLeakAdvance, ite_true]
    refine pmf_map_apply_of_injective _ (fun first second same => ?_) included
    cases first <;> cases second <;> simp_all
  · intro other different
    cases other
    · simp [lateLeakAdvance]
    · exact (different rfl).elim

theorem lateLeakKernel_second_send (profile : LateLeakProfile G late) (secret : LateLeakType)
    (included : Bool) :
    lateLeakKernel profile (.secondLate secret)
        (.answering secret (if included then .secondIncluded else .secondDropped)) =
      lateLeakOpeningLaw profile (.secondLate secret) (some (.opening true)) *
        lateLeakInclusion G included := by
  rw [kernel_sender_apply profile _ _ rfl true]
  · congr 1
    simp only [lateLeakAdvance, ite_true]
    refine pmf_map_apply_of_injective _ (fun first second same => ?_) included
    cases first <;> cases second <;> simp_all
  · intro other different
    cases other
    · cases included <;> simp [lateLeakAdvance]
    · exact (different rfl).elim

/-! ## Canonical histories and information sites -/

/-- The joint action in which the sender opens now or not. -/
def lateLeakSenderJoint (now : Bool) : LateLeakRole → Option LateLeakMove :=
  fun who => if who = .sender then some (.opening now) else none

theorem lateLeak_initial_legal (G : LateLeakParameters) (late : Bool) :
    (lateLeakExecution G late).Legal .initial (fun _ => none) := by
  refine ⟨id, ?_⟩
  intro who
  simp [LateLeakState.actor]

theorem lateLeak_sender_legal (G : LateLeakParameters) (late : Bool) (state : LateLeakState)
    (acting : state.actor = some .sender) (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu late (.full state)) :
    (lateLeakExecution G late).Legal state (lateLeakSenderJoint now) := by
  have running : ¬ state.IsFinished := by
    cases state <;> simp_all [LateLeakState.actor, LateLeakState.IsFinished]
  refine ⟨running, ?_⟩
  intro who
  cases who
  · exact ⟨acting, allowed⟩
  · simp [lateLeakSenderJoint, acting]

/-- The history reaching the protected turn of a type. -/
def lateLeakTypeHistory (G : LateLeakParameters) (late : Bool) (secret : LateLeakType) :
    (lateLeakExecution G late).History :=
  (lateLeakExecution G late).initHistory.extend (lateLeak_initial_legal G late)
    (target := .protectedTurn secret) (by
      change LateLeakState.protectedTurn secret ∈
        (lateLeakAdvance G .initial (none : Option LateLeakMove)).support
      rw [lateLeakAdvance, PMF.support_map]
      exact ⟨secret, (PMF.mem_support_iff _ _).mpr (lateLeakPrior_ne_zero secret), rfl⟩)

theorem lateLeak_open_allowed (late : Bool) (secret : LateLeakType) :
    some (LateLeakMove.opening true) ∈ lateLeakMenu late (.full (.protectedTurn secret)) :=
  ⟨true, rfl, by simp⟩

/-- The history in which a type opens at the protected turn. -/
def lateLeakOpenedHistory (G : LateLeakParameters) (late : Bool) (secret : LateLeakType) :
    (lateLeakExecution G late).History :=
  (lateLeakTypeHistory G late secret).extend
    (lateLeak_sender_legal G late (.protectedTurn secret) rfl true
      (lateLeak_open_allowed late secret))
    (target := .answering secret .protectedOpen) (by
      change _ ∈ (lateLeakAdvance G (.protectedTurn secret) (some (.opening true))).support
      simp [lateLeakAdvance])

/-- The history in which a type waits at the protected turn. -/
def lateLeakFirstHistory (G : LateLeakParameters) (secret : LateLeakType) :
    (lateLeakExecution G true).History :=
  (lateLeakTypeHistory G true secret).extend
    (lateLeak_sender_legal G true (.protectedTurn secret) rfl false ⟨false, rfl, rfl⟩)
    (target := .firstLate secret) (by
      change _ ∈ (lateLeakAdvance G (.protectedTurn secret) (some (.opening false))).support
      simp [lateLeakAdvance])

/-- The history in which a type sends at the first late turn. -/
def lateLeakFirstSentHistory (G : LateLeakParameters) (secret : LateLeakType) (included : Bool) :
    (lateLeakExecution G true).History :=
  (lateLeakFirstHistory G secret).extend
    (lateLeak_sender_legal G true (.firstLate secret) rfl true ⟨true, rfl⟩)
    (target := .answering secret (if included then .firstIncluded else .firstDropped)) (by
      change _ ∈ (lateLeakAdvance G (.firstLate secret) (some (.opening true))).support
      simp only [lateLeakAdvance, ite_true, PMF.support_map]
      exact ⟨included, (PMF.mem_support_iff _ _).mpr (lateLeakInclusion_ne_zero included), rfl⟩)

/-- The history in which a type holds at the first late turn. -/
def lateLeakSecondHistory (G : LateLeakParameters) (secret : LateLeakType) :
    (lateLeakExecution G true).History :=
  (lateLeakFirstHistory G secret).extend
    (lateLeak_sender_legal G true (.firstLate secret) rfl false ⟨false, rfl⟩)
    (target := .secondLate secret) (by
      change _ ∈ (lateLeakAdvance G (.firstLate secret) (some (.opening false))).support
      simp [lateLeakAdvance])

/-- The history in which a type sends at the second late turn. -/
def lateLeakSecondSentHistory (G : LateLeakParameters) (secret : LateLeakType) (included : Bool) :
    (lateLeakExecution G true).History :=
  (lateLeakSecondHistory G secret).extend
    (lateLeak_sender_legal G true (.secondLate secret) rfl true ⟨true, rfl⟩)
    (target := .answering secret (if included then .secondIncluded else .secondDropped)) (by
      change _ ∈ (lateLeakAdvance G (.secondLate secret) (some (.opening true))).support
      simp only [lateLeakAdvance, ite_true, PMF.support_map]
      exact ⟨included, (PMF.mem_support_iff _ _).mpr (lateLeakInclusion_ne_zero included), rfl⟩)

/-- An information site from a decision history. -/
def lateLeakSite (G : LateLeakParameters) (late : Bool) (who : LateLeakRole) (history :
    (lateLeakExecution G late).History)
    (move : LateLeakMove) (menu : some move ∈ lateLeakMenu late (lateLeakView who history.state))
    (running : ¬ history.state.IsFinished) : (lateLeakModel G late).InformationSite who :=
  ⟨lateLeakView who history.state,
    ⟨⟨history, lateLeak_infoOf G late who history.trace⟩, running, move, menu⟩⟩

theorem lateLeak_fiber_view {who : LateLeakRole} {info : LateLeakView}
    (history : (lateLeakModel G late).InformationHistory who info) :
    lateLeakView who history.1.state = info :=
  (lateLeak_infoOf G late who history.1.trace).symm.trans history.2

theorem lateLeak_sender_fiber_state {state : LateLeakState}
    (history : (lateLeakModel G late).InformationHistory .sender (.full state)) :
    history.1.state = state :=
  LateLeakView.full.inj (lateLeak_fiber_view history)

theorem lateLeak_listener_fiber_state {signal : LateLeakSignal}
    (history : (lateLeakModel G late).InformationHistory .listener (.asked signal)) :
    ∃ secret resolution, history.1.state = .answering secret resolution ∧
      lateLeakSignal secret resolution = signal := by
  have view := lateLeak_fiber_view history
  generalize history.1.state = state at view
  cases state with
  | answering secret resolution =>
      exact ⟨secret, resolution, rfl, LateLeakView.asked.inj view⟩
  | _ => simp [lateLeakView] at view

/-! ## Continuation values and rationality -/

instance (late : Bool) (who : LateLeakRole) (info : LateLeakView) :
    Finite ((lateLeakModel G late).InformationHistory who info) :=
  Subtype.finite

/-- A continuation value is the belief average of the five-step value. -/
theorem lateLeak_continuation_value (A : (lateLeakModel G late).BehavioralAssessment)
    (certificate : (lateLeakExecution G late).WellFoundedHistories) {who : LateLeakRole}
    (site : (lateLeakModel G late).InformationSite who)
    (alternative : (lateLeakModel G late).BehavioralPolicy who) :
    (A.continuationContext certificate site (lateLeakPayoff G late who)).value alternative =
      expect (A.belief who site) fun history =>
        lateLeakValue (lateLeakUpdate A.strategy who alternative) (lateLeakStatePayoff G who) 5
          history.1.state := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, expect_bind_of_finite]
  congr 1
  funext history
  rw [lateLeakValue, ← lateLeak_terminal_map_state certificate, expect_map]
  rfl

theorem lateLeak_context_integrable (A : (lateLeakModel G late).BehavioralAssessment)
    (certificate : (lateLeakExecution G late).WellFoundedHistories) {who : LateLeakRole}
    (site : (lateLeakModel G late).InformationSite who)
    (payoff : (lateLeakExecution G late).History → ℝ)
    (alternative : (lateLeakModel G late).BehavioralPolicy who) :
    (A.continuationContext certificate site payoff).IntegrableAt alternative :=
  payoffIntegrable_of_finite _ _

/-- At a sender's information set the continuation value is the five-step
value at its state. -/
theorem lateLeak_sender_context_value (A : (lateLeakModel G late).BehavioralAssessment)
    (certificate : (lateLeakExecution G late).WellFoundedHistories)
    (site : (lateLeakModel G late).InformationSite .sender) {state : LateLeakState}
    (at_state : site.1 = .full state)
    (alternative : (lateLeakModel G late).BehavioralPolicy .sender) :
    (A.continuationContext certificate site (lateLeakPayoff G late .sender)).value alternative =
      lateLeakValue (lateLeakUpdate A.strategy .sender alternative)
        (lateLeakStatePayoff G .sender) 5 state := by
  rw [lateLeak_continuation_value, ← expect_constant (A.belief .sender site)
    (lateLeakValue (lateLeakUpdate A.strategy .sender alternative)
      (lateLeakStatePayoff G .sender) 5 state)]
  apply expect_congr_on_support
  intro history _
  have view : lateLeakView .sender history.1.state = .full state :=
    (lateLeak_fiber_view history).trans at_state
  rw [LateLeakView.full.inj view]

/-- Sequential rationality at a sender's information set compares five-step
values at its state. -/
theorem lateLeak_sender_rational {A : (lateLeakModel G late).BehavioralAssessment}
    {certificate : (lateLeakExecution G late).WellFoundedHistories}
    (rational : A.IsSequentiallyRational certificate (lateLeakPayoff G late))
    (site : (lateLeakModel G late).InformationSite .sender) {state : LateLeakState}
    (at_state : site.1 = .full state)
    (alternative : (lateLeakModel G late).BehavioralPolicy .sender) :
    lateLeakValue (lateLeakUpdate A.strategy .sender alternative)
        (lateLeakStatePayoff G .sender) 5 state ≤
      lateLeakValue A.strategy (lateLeakStatePayoff G .sender) 5 state := by
  have optimal := (Context.isLocallyOptimal_iff_of_integrable
    (lateLeak_context_integrable A certificate site _ _)
    (fun other _ => lateLeak_context_integrable A certificate site _ other)).mp
      (rational .sender site) alternative (Set.mem_univ _)
  rw [lateLeak_sender_context_value A certificate site at_state,
    lateLeak_sender_context_value A certificate site at_state, lateLeakUpdate_self] at optimal
  exact optimal

/-- Conversely, comparing five-step values establishes rationality at a
sender's information set. -/
theorem lateLeak_sender_rational_of_values (A : (lateLeakModel G late).BehavioralAssessment)
    (certificate : (lateLeakExecution G late).WellFoundedHistories)
    (site : (lateLeakModel G late).InformationSite .sender) {state : LateLeakState}
    (at_state : site.1 = .full state)
    (values : ∀ alternative : (lateLeakModel G late).BehavioralPolicy .sender,
      lateLeakValue (lateLeakUpdate A.strategy .sender alternative)
          (lateLeakStatePayoff G .sender) 5 state ≤
        lateLeakValue A.strategy (lateLeakStatePayoff G .sender) 5 state) :
    A.IsSequentiallyRationalAt site
      (A.continuationContext certificate site (lateLeakPayoff G late .sender)) := by
  refine (Context.isLocallyOptimal_iff_of_integrable
    (lateLeak_context_integrable A certificate site _ _)
    (fun other _ => lateLeak_context_integrable A certificate site _ other)).mpr ?_
  intro alternative _
  rw [lateLeak_sender_context_value A certificate site at_state,
    lateLeak_sender_context_value A certificate site at_state, lateLeakUpdate_self]
  exact values alternative

/-- The state an answer leads to. -/
def lateLeakAnswered : LateLeakState → Option LateLeakMove → LateLeakState
  | .answering secret resolution, choice => .finished secret resolution (lateLeakReplyOf choice)
  | state, _ => state

/-- The listener's decision problem at one of its information sets. -/
def lateLeakListenerDecision (G : LateLeakParameters) (late : Bool) (site :
    (lateLeakModel G late).InformationSite .listener)
    (signal : LateLeakSignal) (at_signal : site.1 = .asked signal)
    (base : (lateLeakModel G late).BehavioralPolicy .listener) :
    (lateLeakModel G late).ContinuationDecision (lateLeakPayoff G late)
      ((lateLeakModel G late).runBehavioralTerminalFrom (lateLeak_terminates G late)) LateLeakState
      ((lateLeakModel G late).Choice .listener site.1) where
  player := .listener
  site := site
  state history := history.1.state
  response profile := profile .listener site.1
  response_finite _ := Set.toFinite _
  reward state choice := lateLeakStatePayoff G .listener (lateLeakAnswered state choice.1)
  policy choice := base.commit site.1 choice
  history_value profile history := by
    have mapped := lateLeak_terminal_map_state (lateLeak_terminates G late) profile history.1
    rw [show (lateLeakPayoff G late .listener) =
      (lateLeakStatePayoff G .listener) ∘ ExecutionProtocol.History.state from rfl,
      ← expect_map, mapped]
    obtain ⟨secret, resolution, state_eq, signal_eq⟩ :=
      lateLeak_listener_fiber_state (late := late) (signal := signal) ⟨history.1, by
        rw [history.2, at_signal]⟩
    change lateLeakValue profile (lateLeakStatePayoff G .listener) (4 + 1) history.1.state = _
    rw [state_eq, lateLeakValue_answering, lateLeakAnswerValue, lateLeakReplyLaw, signal_eq,
      ← at_signal, expect_map]
    rfl
  realize profile choice := by
    simp only [Profile.update_same, InformationModel.BehavioralPolicy.commit_self]

end Vegas
