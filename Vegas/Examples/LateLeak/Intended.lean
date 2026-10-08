/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Impossibility
import GameTheoryExtensions.Analysis.Protocol.LastDecision
import Mathlib.Probability.Distributions.Uniform

/-! # The intended game

In the intended game the sender can only open at the protected turn. The
listener's belief after the opening is the prior over labels, uniform within
the committed bit's class, so every label guess is worth `1/3` while the safe
answer is worth `2/5`. The assessment in which the listener answers safely,
with the Bayes beliefs of a uniformly mixed profile, is a sequential
equilibrium, and every sequential equilibrium has the intended outcome law.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter

variable {G : LateLeakParameters}

/-! ## Play of the intended game -/

/-- In the intended game the sender opens at the protected turn. -/
theorem lateLeak_intended_opening (profile : LateLeakProfile G false) (secret : LateLeakType) :
    lateLeakOpeningLaw profile (.protectedTurn secret) = PMF.pure (some (.opening true)) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro choice supported
  rw [lateLeakOpeningLaw, PMF.mem_support_map_iff] at supported
  obtain ⟨option, _, rfl⟩ := supported
  obtain ⟨now, same, allowed⟩ := option.2
  cases now
  · simp at allowed
  · exact same

theorem lateLeak_intended_openProb (profile : LateLeakProfile G false) (secret : LateLeakType) :
    lateLeakOpenProb profile (.protectedTurn secret) = 1 := by
  simp [lateLeakOpenProb, lateLeak_intended_opening]

/-- The states the intended game reaches. -/
def LateLeakState.OnIntendedPath : LateLeakState → Prop
  | .initial | .protectedTurn _ => True
  | .answering _ .protectedOpen => True
  | .finished _ .protectedOpen _ => True
  | _ => False

theorem lateLeak_intended_path :
    ∀ {state : LateLeakState} (_ : (lateLeakExecution G false).Trace state),
      state.OnIntendedPath
  | _, .start => trivial
  | _, .extend (source := source) (target := target) prior joint legal realized => by
      have earlier := lateLeak_intended_path prior
      change target ∈ (lateLeakAdvance G source (joint source.mover)).support at realized
      cases source with
      | initial =>
          rw [lateLeakAdvance, PMF.support_map] at realized
          obtain ⟨_, _, rfl⟩ := realized
          trivial
      | protectedTurn secret =>
          obtain ⟨move, chosen, menu⟩ := lateLeak_mover_choice_of_legal legal (who := .sender) rfl
          obtain ⟨now, same, allowed⟩ := menu
          obtain rfl := Option.some.inj same
          cases now
          · simp at allowed
          · simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, chosen,
              lateLeakAdvance, ite_true, PMF.mem_support_pure_iff] at realized
            subst realized
            trivial
      | answering secret resolution =>
          simp only [lateLeakAdvance, PMF.mem_support_pure_iff] at realized
          subst realized
          cases resolution <;> simp_all [LateLeakState.OnIntendedPath]
      | finished => exact (legal.1 trivial).elim
      | firstLate => exact earlier.elim
      | secondLate => exact earlier.elim

/-- The sender's information sets in the intended game are its protected
turns. -/
theorem lateLeak_intended_sender_site (site : (lateLeakModel G false).InformationSite .sender) :
    ∃ secret, site.1 = .full (.protectedTurn secret) := by
  obtain ⟨history, _, move, menu⟩ := site.2
  have view := lateLeak_fiber_view history
  have path := lateLeak_intended_path history.1.trace
  rw [← view] at menu ⊢
  generalize history.1.state = state at menu path
  cases state with
  | protectedTurn secret => exact ⟨secret, rfl⟩
  | answering secret resolution => simp [lateLeakView, lateLeakMenu] at menu
  | finished => simp [lateLeakView, lateLeakMenu] at menu
  | initial => simp [lateLeakView, lateLeakMenu] at menu
  | _ => exact path.elim

/-- The listener's information sets in the intended game follow protected
openings. -/
theorem lateLeak_intended_listener_site
    (site : (lateLeakModel G false).InformationSite .listener) :
    ∃ bit, site.1 = .asked (.protectedSuccess bit) := by
  obtain ⟨history, _, move, menu⟩ := site.2
  have view := lateLeak_fiber_view history
  have path := lateLeak_intended_path history.1.trace
  rw [← view] at menu ⊢
  generalize history.1.state = state at menu path
  cases state with
  | answering secret resolution =>
      cases resolution
      · exact ⟨secret.1, rfl⟩
      all_goals exact path.elim
  | _ => simp [lateLeakView, lateLeakMenu] at menu

/-! ## The listener after a protected opening -/

/-- The history of the intended game in which a type opened. -/
def lateLeakOpenedMember (G : LateLeakParameters) (secret : LateLeakType) :
    (lateLeakModel G false).InformationHistory .listener (.asked (.protectedSuccess secret.1)) :=
  lateLeakListenerMember G false (lateLeakOpenedHistory G false secret) (.protectedSuccess secret.1)
    rfl

theorem lateLeak_intended_weight_opened (profile : LateLeakProfile G false)
    (secret : LateLeakType) :
    (lateLeakModel G false).historyReachWeight profile (lateLeakOpenedHistory G false secret) =
      lateLeakPrior secret := by
  rw [lateLeak_weight_opened, lateLeak_intended_opening, PMF.pure_apply_self, mul_one]

/-- Bayes' rule after a protected opening gives every label of the class the
same belief. -/
theorem lateLeak_intended_bayes_uniform (B : (lateLeakModel G false).BehavioralAssessment)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent _ B
      (lateLeak_antichain G false)) (bit : Bool)
    (decision : (lateLeakModel G false).IsDecisionInfo .listener (.asked (.protectedSuccess bit)))
    (label other : LateLeakLabel) :
    B.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, label)) =
      B.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, other)) := by
  have mass : 0 < (lateLeakModel G false).informationMass B.strategy .listener ⟨_, decision⟩ := by
    refine ((lateLeakModel G false).informationMass_pos_iff _ _ _).mpr
      ⟨lateLeakOpenedMember G (bit, label), ?_⟩
    change 0 < (lateLeakModel G false).historyReachWeight B.strategy
      (lateLeakOpenedHistory G false (bit, label))
    rw [lateLeak_intended_weight_opened]
    exact pos_iff_ne_zero.mpr (lateLeakPrior_ne_zero _)
  rw [bayes .listener ⟨_, decision⟩ mass, bayes .listener ⟨_, decision⟩ mass]
  change (lateLeakModel G false).historyReachWeight B.strategy
      (lateLeakOpenedHistory G false (bit, label)) / _ =
    (lateLeakModel G false).historyReachWeight B.strategy
      (lateLeakOpenedHistory G false (bit, other)) / _
  rw [lateLeak_intended_weight_opened, lateLeak_intended_weight_opened]
  rfl

/-- With equal beliefs over labels, every label guess is worth `1/3`. -/
theorem lateLeak_intended_guess_reward (A : (lateLeakModel G false).BehavioralAssessment)
    (bit : Bool)
    (decision : (lateLeakModel G false).IsDecisionInfo .listener (.asked (.protectedSuccess bit)))
    (uniform : ∀ label other : LateLeakLabel,
      A.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, label)) =
        A.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, other)))
    (label : LateLeakLabel) :
    lateLeakAnswerReward A ⟨_, decision⟩ (.guess label) = 1 / 3 := by
  have reward (other : LateLeakLabel) :
      lateLeakAnswerReward A ⟨_, decision⟩ (.guess other) =
        (A.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, .a))).toReal := by
    rw [← uniform other .a]
    exact lateLeak_guess_reward_eq A ⟨_, decision⟩ (.protectedSuccess bit) rfl rfl
      (lateLeakOpenedMember G (bit, other)) (bit, other) .protectedOpen rfl
  have total := lateLeak_guess_rewards_total A ⟨_, decision⟩ (.protectedSuccess bit) rfl rfl
  rw [reward, reward, reward] at total
  rw [reward]
  linarith

/-- A sequentially rational listener with equal beliefs over labels answers
safely after a protected opening. -/
theorem lateLeak_intended_listener_safe {A : (lateLeakModel G false).BehavioralAssessment}
    (rational : A.IsSequentiallyRational (lateLeak_terminates G false) (lateLeakPayoff G false))
    (bit : Bool)
    (decision : (lateLeakModel G false).IsDecisionInfo .listener (.asked (.protectedSuccess bit)))
    (uniform : ∀ label other : LateLeakLabel,
      A.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, label)) =
        A.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, other))) :
    lateLeakReplyLaw A.strategy (.protectedSuccess bit) = PMF.pure (some (.reply .safe)) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro choice supported
  obtain ⟨answer, rfl, fits⟩ := lateLeakReplyLaw_support A.strategy _ choice supported
  cases answer with
  | safe => rfl
  | guess label =>
      have maximal := lateLeak_listener_support_maximal rational ⟨_, decision⟩ _ rfl
        (.guess label) .safe fits rfl ((PMF.mem_support_iff _ _).mp supported)
      rw [lateLeak_safe_reward A ⟨_, decision⟩ _ rfl rfl,
        lateLeak_intended_guess_reward A bit decision uniform] at maximal
      norm_num at maximal
  | failure bit => simp [LateLeakAnswer.fits, LateLeakSignal.success] at fits

/-! ## The intended outcome -/

theorem lateLeakFlow_iterate_finished (profile : LateLeakProfile G false) (fuel : ℕ)
    (secret : LateLeakType) (resolution : LateLeakResolution) (answer : LateLeakAnswer) :
    (lateLeakFlow profile)^[fuel] (PMF.pure (.finished secret resolution answer)) =
      PMF.pure (.finished secret resolution answer) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply, lateLeakFlow_pure, lateLeakKernel_finished, ih]

/-- A profile answering safely after every protected opening has the intended
outcome law. -/
theorem lateLeakOutcomeLaw_of_safe (profile : LateLeakProfile G false)
    (safe : ∀ bit, lateLeakReplyLaw profile (.protectedSuccess bit) =
      PMF.pure (some (.reply .safe))) :
    lateLeakOutcomeLaw G false profile = lateLeakIntendedOutcome := by
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
  rw [lateLeak_intended_opening, PMF.pure_bind]
  simp only [lateLeakAdvance, ite_true]
  rw [Function.iterate_succ_apply, lateLeakFlow_pure]
  change (lateLeakFlow profile)^[2]
    ((lateLeakReplyLaw profile (lateLeakSignal secret .protectedOpen)).bind
      (lateLeakAdvance G (.answering secret .protectedOpen))) = _
  rw [lateLeakSignal, safe, PMF.pure_bind]
  simp only [lateLeakAdvance, lateLeakReplyOf]
  exact lateLeakFlow_iterate_finished profile 2 _ _ _

/-! ## An intended sequential equilibrium -/

instance (late : Bool) (who : LateLeakRole) (info : LateLeakView) :
    Finite ((lateLeakModel G late).Choice who info) :=
  Subtype.finite

instance (late : Bool) (who : LateLeakRole) (info : LateLeakView) :
    Nonempty ((lateLeakModel G late).Choice who info) := by
  change Nonempty {choice // choice ∈ lateLeakMenu late info}
  cases info with
  | full state =>
      cases state with
      | protectedTurn secret => exact ⟨⟨some (.opening true), ⟨true, rfl, by simp⟩⟩⟩
      | firstLate secret => exact ⟨⟨some (.opening true), ⟨true, rfl⟩⟩⟩
      | secondLate secret => exact ⟨⟨some (.opening true), ⟨true, rfl⟩⟩⟩
      | initial => exact ⟨⟨none, rfl⟩⟩
      | answering => exact ⟨⟨none, rfl⟩⟩
      | finished => exact ⟨⟨none, rfl⟩⟩
  | idle => exact ⟨⟨none, rfl⟩⟩
  | answered => exact ⟨⟨none, rfl⟩⟩
  | asked signal =>
      by_cases success : signal.success
      · exact ⟨⟨some (.reply .safe), ⟨.safe, rfl, lateLeak_safe_fits success⟩⟩⟩
      · exact ⟨⟨some (.reply (.failure true)), ⟨.failure true, rfl, by
          simpa [LateLeakAnswer.fits] using success⟩⟩⟩

/-- Every option equally likely at every information state. -/
def lateLeakUniformProfile (G : LateLeakParameters)
    (late : Bool) : LateLeakProfile G late := fun _ _ =>
  letI := Fintype.ofFinite
  PMF.uniformOfFintype _

theorem lateLeakUniformProfile_mixed (G : LateLeakParameters) (late : Bool) (who : LateLeakRole)
    (site : (lateLeakModel G late).InformationSite who)
    (choice : (lateLeakModel G late).Choice who site.1) :
    choice ∈ (lateLeakUniformProfile G late who site.1).support := by
  let _ := Fintype.ofFinite ((lateLeakModel G late).Choice who site.1)
  exact PMF.mem_support_uniformOfFintype choice

/-- The listener's safe answer after every success. -/
def lateLeakSafePolicy (G : LateLeakParameters) (late : Bool) :
    (lateLeakModel G late).BehavioralPolicy .listener :=
  fun info =>
    match info with
    | .asked signal =>
        if success : signal.success then
          PMF.pure ⟨some (.reply .safe), ⟨.safe, rfl, lateLeak_safe_fits success⟩⟩
        else lateLeakUniformProfile G late .listener (.asked signal)
    | other => lateLeakUniformProfile G late .listener other

theorem lateLeakKernel_update_listener (profile : LateLeakProfile G false)
    (policy : (lateLeakModel G false).BehavioralPolicy .listener) (state : LateLeakState)
    (mover : state.mover = .sender) :
    lateLeakKernel (lateLeakUpdate profile .listener policy) state =
      lateLeakKernel profile state := by
  unfold lateLeakKernel lateLeakMoveLaw
  rw [mover]
  simp only [lateLeakUpdate, Profile.update_of_ne _ _ (by decide :
    LateLeakRole.sender ≠ LateLeakRole.listener)]

/-- The listener's policy does not change the weight of any history before
play stops. -/
theorem lateLeak_weight_update_listener (profile : LateLeakProfile G false)
    (policy : (lateLeakModel G false).BehavioralPolicy .listener) :
    ∀ {state : LateLeakState} (trace : (lateLeakExecution G false).Trace state),
      ¬ state.IsFinished →
      (lateLeakModel G false).historyReachWeight (lateLeakUpdate profile .listener policy)
          ⟨state, trace⟩ =
        (lateLeakModel G false).historyReachWeight profile ⟨state, trace⟩
  | _, .start, _ => (lateLeak_reachWeight_init _).trans (lateLeak_reachWeight_init _).symm
  | _, .extend (source := source) (target := target) prior joint legal realized, running => by
      rw [lateLeak_reachWeight_step _ ⟨target, .extend prior joint legal realized⟩
          (Nat.succ_pos _),
        lateLeak_reachWeight_step _ ⟨target, .extend prior joint legal realized⟩
          (Nat.succ_pos _)]
      change (lateLeakModel G false).historyReachWeight _ ⟨source, prior⟩ *
          lateLeakKernel _ source target =
        (lateLeakModel G false).historyReachWeight _ ⟨source, prior⟩ *
          lateLeakKernel _ source target
      have mover : source.mover = .sender := by
        change target ∈ (lateLeakAdvance G source (joint source.mover)).support at realized
        cases source with
        | answering secret resolution =>
            simp only [lateLeakAdvance, PMF.mem_support_pure_iff] at realized
            subst realized
            exact (running trivial).elim
        | _ => rfl
      rw [lateLeak_weight_update_listener profile policy prior legal.1,
        lateLeakKernel_update_listener profile policy source mover]

theorem lateLeak_fiber_not_finished {late : Bool} {who : LateLeakRole}
    (site : (lateLeakModel G late).InformationSite who)
    (history : (lateLeakModel G late).InformationHistory who site.1) :
    ¬ history.1.state.IsFinished := by
  obtain ⟨_, _, move, menu⟩ := site.2
  have view := lateLeak_fiber_view history
  rw [← view] at menu
  intro finished
  generalize history.1.state = state at menu finished
  cases state <;> cases who <;> simp_all [lateLeakView, lateLeakMenu, LateLeakState.IsFinished]

/-- The intended sequential equilibrium: the sender opens at the protected
turn, the listener answers safely, and beliefs are the Bayes beliefs of the
uniformly mixed profile. -/
def lateLeakIntendedAssessment (G : LateLeakParameters) :
    (lateLeakModel G false).BehavioralAssessment :=
  ⟨lateLeakUpdate (lateLeakUniformProfile G false) .listener (lateLeakSafePolicy G false),
    ((lateLeakModel G false).bayesAssessment (lateLeakUniformProfile G false)
      (lateLeakUniformProfile_mixed G false) (lateLeak_antichain G false)).belief⟩

theorem lateLeakIntendedAssessment_safe (bit : Bool) :
    lateLeakReplyLaw (lateLeakIntendedAssessment G).strategy (.protectedSuccess bit) =
      PMF.pure (some (.reply .safe)) := by
  simp [lateLeakReplyLaw, lateLeakIntendedAssessment, lateLeakUpdate, lateLeakSafePolicy,
    LateLeakSignal.success, PMF.pure_map]

theorem lateLeakIntendedAssessment_isSequentialEquilibrium :
    (lateLeakIntendedAssessment G).IsSequentialEquilibrium (lateLeak_antichain G false)
      (lateLeak_terminates G false) (lateLeakPayoff G false) := by
  let reference : (lateLeakModel G false).BehavioralAssessment :=
    InformationModel.BehavioralAssessment.ofStrategy (lateLeakUniformProfile G false)
  have mixed : reference.IsFullyMixed := lateLeakUniformProfile_mixed G false
  refine ⟨?_, ?_⟩
  · intro who site
    cases who with
    | sender =>
        obtain ⟨secret, at_state⟩ := lateLeak_intended_sender_site site
        apply lateLeak_sender_rational_of_values _ _ site at_state
        intro alternative
        rw [show (5 : ℕ) = 1 + 4 from rfl, lateLeakValue_protectedTurn,
          lateLeakValue_protectedTurn, lateLeakProtectedValue, lateLeakProtectedValue,
          lateLeak_intended_openProb, lateLeak_intended_openProb,
          lateLeakAnswerValue_update_sender]
        simp
    | listener =>
        obtain ⟨bit, at_signal⟩ := lateLeak_intended_listener_site site
        rcases site with ⟨info, decision⟩
        change info = _ at at_signal
        subst at_signal
        let problem := lateLeakListenerDecision G false ⟨_, decision⟩ (.protectedSuccess bit) rfl
          (lateLeakSafePolicy G false)
        refine (problem.rationalAt_iff_support_maximal (lateLeakIntendedAssessment G)).mpr ?_
        intro choice supported other
        have uniform := lateLeak_intended_bayes_uniform
          ((lateLeakModel G false).bayesAssessment (lateLeakUniformProfile G false)
            (lateLeakUniformProfile_mixed G false) (lateLeak_antichain G false))
          ((lateLeakModel G false).bayesAssessment_isBayesConsistent _ _ _) bit decision
        have law : (lateLeakIntendedAssessment G).strategy .listener
            (.asked (.protectedSuccess bit)) =
            PMF.pure ⟨some (.reply .safe), ⟨.safe, rfl, rfl⟩⟩ := by
          simp [lateLeakIntendedAssessment, lateLeakUpdate, lateLeakSafePolicy,
            LateLeakSignal.success]
        change choice ∈ ((lateLeakIntendedAssessment G).strategy .listener
          (.asked (.protectedSuccess bit))).support at supported
        rw [law, PMF.mem_support_pure_iff] at supported
        subst supported
        obtain ⟨answer, same, fits⟩ := other.2
        rw [lateLeakListenerDecision_expectedReward G _ _ _ _ _ _ other answer same,
          lateLeakListenerDecision_expectedReward G _ _ _ _ _ _ _ .safe rfl,
          lateLeak_safe_reward _ _ _ rfl rfl]
        cases answer with
        | safe => rw [lateLeak_safe_reward _ _ _ rfl rfl]
        | guess label =>
            rw [lateLeak_intended_guess_reward (lateLeakIntendedAssessment G) bit decision uniform]
            norm_num
        | failure => simp [LateLeakAnswer.fits, LateLeakSignal.success] at fits
  · have reach : ∀ (alternative : (lateLeakModel G false).BehavioralPolicy .listener)
        (player : LateLeakRole) (site : (lateLeakModel G false).InformationSite player)
        (history : (lateLeakModel G false).InformationHistory player site.1),
        (lateLeakModel G false).historyReachWeight
          (Profile.update (sig := (lateLeakModel G false).behavioralSignature)
            reference.strategy .listener alternative) history.1 =
          (lateLeakModel G false).historyReachWeight reference.strategy history.1 :=
      by
        intro alternative player site history
        exact lateLeak_weight_update_listener reference.strategy alternative history.1.trace
          (lateLeak_fiber_not_finished site history)
    exact InformationModel.consistent_update_of_reach_invariant reference mixed
      (lateLeak_antichain G false) .listener reach (lateLeakSafePolicy G false)

/-- Every sequential equilibrium of the intended game has the intended outcome
law. -/
theorem lateLeak_intended_outcome (A : (lateLeakModel G false).BehavioralAssessment)
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain G false)
      (lateLeak_terminates G false) (lateLeakPayoff G false)) :
    lateLeakOutcomeLaw G false A.strategy = lateLeakIntendedOutcome := by
  obtain ⟨rational, sequence, approximate, converges⟩ := equilibrium
  apply lateLeakOutcomeLaw_of_safe
  intro bit
  have decision : (lateLeakModel G false).IsDecisionInfo .listener
      (.asked (.protectedSuccess bit)) :=
    (lateLeakListenerSite G false (lateLeakOpenedHistory G false (bit, .a)) (.protectedSuccess bit)
      rfl .safe rfl).2
  apply lateLeak_intended_listener_safe rational bit decision
  intro label other
  have same (n : ℕ) := lateLeak_intended_bayes_uniform (sequence n) (approximate n).2 bit
    decision label other
  have first := converges.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, label))
  have second := converges.belief .listener ⟨_, decision⟩ (lateLeakOpenedMember G (bit, other))
  simp only [same] at first
  exact tendsto_nhds_unique first second

/-- **The intended game.** It has a sequential equilibrium, and every
sequential equilibrium has the intended outcome law: every type opens at the
protected turn and the listener answers safely. -/
theorem lateLeak_intended_equilibria (G : LateLeakParameters) :
    (∃ A : (lateLeakModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G false) (lateLeak_terminates G false)
        (lateLeakPayoff G false)) ∧
    ∀ A : (lateLeakModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G false) (lateLeak_terminates G false)
          (lateLeakPayoff G false) →
        lateLeakOutcomeLaw G false A.strategy = lateLeakIntendedOutcome :=
  ⟨⟨lateLeakIntendedAssessment G, lateLeakIntendedAssessment_isSequentialEquilibrium⟩,
    lateLeak_intended_outcome⟩

end Vegas
