/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.BeliefMonomial
import GameTheory.Protocol.StateKernel
import GameTheoryExtensions.Analysis.Protocol.ReachBounds
import Mathlib.Probability.Distributions.Uniform

/-! # Shared trembles rule out cyclic pairwise beliefs

Nature chooses one of three pairs. The sender cannot observe the pair and
chooses a main action or one of three rare actions. The observer is asked to
move exactly when the rare action belongs to the selected pair; it sees the
pair but not the sender's action. Thus all three observer information sets use
the same behavioral probabilities. All utilities are zero.
-/

noncomputable section

namespace GameTheoryExtensionsTests.CyclicBeliefs

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Filter

inductive State
  | initial
  | choosing (excluded : Fin 3)
  | asked (excluded actual : Fin 3)
  | done
  deriving DecidableEq, Fintype

inductive View
  | idle
  | choose
  | pair (excluded : Fin 3)
  deriving DecidableEq, Fintype

def State.actor : State → Option Bool
  | .choosing _ => some false
  | .asked .. => some true
  | _ => none

def view (who : Bool) : State → View
  | .choosing _ => if who then .idle else .choose
  | .asked excluded _ => if who then .pair excluded else .idle
  | _ => .idle

def menu : View → Set (Option (Fin 4))
  | .idle => {none}
  | .choose => {move | ∃ action, move = some action}
  | .pair _ => {move | ∃ action, move = some action}

def advance : State → Option (Fin 4) → PMF State
  | .initial, _ => (PMF.uniformOfFintype (Fin 3)).map State.choosing
  | .choosing excluded, some action =>
      match Fin.cases none some action with
      | none => PMF.pure .done
      | some actual => PMF.pure (if actual = excluded then .done else .asked excluded actual)
  | _, _ => PMF.pure .done

@[reducible]
def arena : ExecutionProtocol Bool where
  State := State
  Action _ := Fin 4
  init := .initial
  active state who := state.actor = some who
  available state who := {action | some action ∈ menu (view who state)}
  terminal state := state = .done
  step state joint := advance state (joint.1 (state.actor.getD false))
  progress state running := by
    refine ⟨fun who => if state.actor = some who then some 0 else none, ?_⟩
    intro who
    cases state <;> cases who <;> simp_all [State.actor, view, menu]

@[reducible]
def signals : InfoSignals arena where
  PublicSignal := Unit
  PrivateSignal _ := View
  initialPublic := ()
  initialPrivate _ := .idle
  publicSignal _ := ()
  privateSignal who event := view who event.target
  InfoState _ := View
  initInfo _ signal _ := signal
  pushInfo _ _ _ signal _ := signal

theorem info_state (who : Bool) : ∀ {state} (trace : arena.Trace state),
    signals.infoOf who trace = view who state
  | _, .start => rfl
  | _, .extend .. => rfl

@[reducible]
def model : InformationModel arena where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate who state trace choice := by
    rw [info_state]
    cases who <;> cases state <;> cases choice <;>
      simp [LegalOption, State.actor, view, menu]

instance (who : Bool) : DecidableEq (model.InfoState who) := inferInstanceAs (DecidableEq View)

def State.depth : State → Nat
  | .initial => 0
  | .choosing _ => 1
  | .asked .. => 2
  | .done => 3

theorem trace_depth {state : arena.State} (trace : arena.Trace state)
    (running : state ≠ .done) : trace.length = state.depth := by
  refine @Trace.rec Bool arena
    (fun state trace => state ≠ .done → trace.length = state.depth)
    (fun _ => rfl) ?_ state trace running
  intro source target prior joint legal realized ih running
  cases source with
  | initial =>
      change target ∈ ((PMF.uniformOfFintype (Fin 3)).map State.choosing).support at realized
      obtain ⟨excluded, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
      simp only [Trace.length, State.depth]
      exact congrArg (· + 1) (ih (by simp))
  | choosing excluded =>
      change target ∈ (advance (.choosing excluded) (joint false)).support at realized
      cases moved : joint false with
      | none => exact (running (by simpa [advance, moved] using realized)).elim
      | some action =>
          obtain rfl | ⟨actual, rfl⟩ := Fin.eq_zero_or_eq_succ action
          · exact (running (by simpa [advance, moved] using realized)).elim
          · simp only [advance, moved, Fin.cases_succ, PMF.support_pure,
              Set.mem_singleton_iff] at realized
            by_cases same : actual = excluded
            · simp only [same, ↓reduceIte] at realized
              exact (running realized).elim
            · simp only [same, ↓reduceIte] at realized
              subst target
              simp only [Trace.length, State.depth]
              exact congrArg (· + 1) (ih (by simp))
  | asked excluded actual =>
      have : target = .done := by simpa [arena, advance] using realized
      exact (running this).elim
  | done => exact (legal.1 rfl).elim

theorem bounded : arena.BoundedHorizon 3 := by
  intro state trace long
  by_contra running
  have depth := trace_depth trace running
  cases state <;> simp_all [State.depth]

def rootJoint (action : Fin 4) : Bool → Option (Fin 4)
  | false => some action
  | true => none

theorem rootJoint_legal (excluded : Fin 3) (action : Fin 4) :
    arena.Legal (.choosing excluded) (rootJoint action) := by
  refine ⟨by simp, ?_⟩
  intro who
  cases who <;> simp [arena, State.actor, view, menu, rootJoint]

theorem initial_legal : arena.Legal .initial arena.noop := by
  exact arena.noop_isLegal (by decide) (by intro who; cases who <;> decide)

def rootTrace (excluded : Fin 3) : arena.Trace (.choosing excluded) :=
  .extend .start arena.noop initial_legal
    ((PMF.mem_support_map_iff _ _ _).mpr
      ⟨excluded, PMF.mem_support_uniformOfFintype excluded, rfl⟩)

def rootHistory (excluded : Fin 3) : arena.History := ⟨_, rootTrace excluded⟩

def pairTrace (excluded actual : Fin 3) (fits : actual ≠ excluded) :
    arena.Trace (.asked excluded actual) :=
  .extend (rootTrace excluded) (rootJoint actual.succ) (rootJoint_legal excluded actual.succ)
    (by simp [arena, advance, rootJoint, State.actor, fits])

def pairHistory (excluded actual : Fin 3) (fits : actual ≠ excluded) : arena.History :=
  ⟨_, pairTrace excluded actual fits⟩

def pairSite (excluded : Fin 3) : model.InformationSite true :=
  ⟨.pair excluded, ⟨⟨pairHistory excluded (excluded + 1) (by fin_cases excluded <;> decide), rfl⟩,
    by simp [arena, pairHistory], 0, ⟨0, rfl⟩⟩⟩

def pairMember (excluded actual : Fin 3) (fits : actual ≠ excluded) :
    model.InformationHistory true (pairSite excluded).1 := ⟨pairHistory excluded actual fits, rfl⟩

theorem decision_depth (who : Bool) (site : model.InformationSite who)
    (history : model.InformationHistory who site.1) :
    history.1.trace.length = if who then 2 else 1 := by
  have active : history.1.state.actor = some who := InformationSite.active model site history
  have running : history.1.state ≠ .done := by
    intro stopped
    simp only [stopped, State.actor] at active
    cases active
  rw [trace_depth history.1.trace running]
  cases state : history.1.state <;> cases who <;> simp_all [State.actor, State.depth]

theorem antichain : model.DecisionInformationAntichain := by
  intro who site first second joint legal reached realized fuel reach
  have monotone := reach.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at monotone
  have firstDepth := decision_depth who site first
  have secondDepth := decision_depth who site second
  omega

instance (who : Bool) (info : View) : Fintype (model.Choice who info) := Fintype.ofFinite _

instance (who : Bool) (info : View) : Nonempty (model.Choice who info) := by
  cases info with
  | idle => exact ⟨⟨none, rfl⟩⟩
  | choose => exact ⟨⟨some 0, ⟨0, rfl⟩⟩⟩
  | pair excluded => exact ⟨⟨some 0, ⟨0, rfl⟩⟩⟩

def uniformStrategy (who : Bool) (info : model.InfoState who) : PMF (model.Choice who info) :=
  PMF.uniformOfFintype _

theorem uniform_full (who : Bool) (site : model.InformationSite who)
    (choice : model.Choice who site.1) : choice ∈ (uniformStrategy who site.1).support :=
  PMF.mem_support_uniformOfFintype choice

def uniformAssessment : model.BehavioralAssessment :=
  model.bayesAssessment uniformStrategy uniform_full antichain

/-- The inconsistent cyclic support does not imply nonexistence of equilibrium. -/
theorem uniform_sequential_equilibrium :
    uniformAssessment.IsSequentialEquilibrium antichain bounded.wellFoundedHistories
      (fun _ _ => 0) :=
  ⟨uniformAssessment.isSequentiallyRational_zero _,
    BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes antichain
      (model.bayesAssessment_isFullyMixed _ uniform_full antichain)
      (model.bayesAssessment_isBayesConsistent _ uniform_full antichain)⟩

open scoped ENNReal

def rootChoice (action : Fin 4) : model.Choice false .choose := ⟨some action, ⟨action, rfl⟩⟩

theorem root_weight (profile : ∀ who, model.BehavioralPolicy who) (excluded : Fin 3) :
    (model.historyReachWeight profile (rootHistory excluded)).toReal = 1 / 3 := by
  unfold rootHistory rootTrace
  rw [model.historyReachProbability_extend]
  change (model.historyReachWeight profile arena.initHistory).toReal * _ = _
  rw [model.historyReachWeight_initHistory]
  simp only [ENNReal.toReal_one, one_mul, stepProb]
  rw [model.behavioralJoint_eq_pure_of_no_active profile .start initial_legal.1
    (by intro who; cases who <;> simp [State.actor])]
  change ((PMF.pure ⟨arena.noop, initial_legal⟩ :
    PMF {joint : Bool → Option (Fin 4) // arena.Legal .initial joint})
      ⟨arena.noop, initial_legal⟩).toReal *
    (((PMF.uniformOfFintype (Fin 3)).map State.choosing) (.choosing excluded)).toReal = _
  rw [PMF.pure_apply_self, ENNReal.toReal_one, one_mul]
  rw [pmf_map_apply_of_injective _ (fun _ _ same => State.choosing.inj same),
    PMF.uniformOfFintype_apply]
  norm_num

theorem pair_weight (profile : ∀ who, model.BehavioralPolicy who) (excluded actual : Fin 3)
    (fits : actual ≠ excluded) :
    (model.historyReachWeight profile (pairHistory excluded actual fits)).toReal =
      (1 / 3) * (profile false .choose (rootChoice actual.succ)).toReal := by
  unfold pairHistory pairTrace
  rw [model.historyReachProbability_extend]
  change (model.historyReachWeight profile (rootHistory excluded)).toReal * _ = _
  rw [root_weight]
  congr 1
  unfold stepProb
  rw [model.behavioralJoint_prob_eq_prod]
  simp only [Fintype.prod_bool]
  change ((profile true .idle) ⟨none, rfl⟩).toReal *
    (profile false .choose (rootChoice actual.succ)).toReal *
      ((advance (.choosing excluded) (some actual.succ)) (.asked excluded actual)).toReal = _
  let : Subsingleton (model.Choice true .idle) :=
    ⟨fun first second => Subtype.ext (first.2.trans second.2.symm)⟩
  rw [eq_pure_of_subsingleton (profile true .idle) ⟨none, rfl⟩]
  simp [advance, fits]

def favoredMember (excluded : Fin 3) : model.InformationHistory true (pairSite excluded).1 :=
  pairMember excluded (excluded + 1) (by fin_cases excluded <;> decide)

def opposedMember (excluded : Fin 3) : model.InformationHistory true (pairSite excluded).1 :=
  pairMember excluded (excluded + 2) (by fin_cases excluded <;> decide)

theorem reach_cycle (profile : ∀ who, model.BehavioralPolicy who) :
    ∏ excluded, (model.historyReachWeight profile (favoredMember excluded).1).toReal =
      ∏ excluded, (model.historyReachWeight profile (opposedMember excluded).1).toReal := by
  simp only [favoredMember, opposedMember, pairMember, pair_weight, Fin.prod_univ_three]
  norm_num
  ring

/-- Shared root probabilities constrain every common fully mixed Bayes sequence. -/
theorem consistent_cycle {assessment : model.BehavioralAssessment}
    (consistent : assessment.IsSequentiallyConsistent antichain) :
    ∏ excluded, (assessment.belief true (pairSite excluded) (favoredMember excluded)).toReal =
      ∏ excluded, (assessment.belief true (pairSite excluded) (opposedMember excluded)).toReal :=
  consistent.belief_prod_eq (fun _ : Fin 3 => true) pairSite favoredMember opposedMember reach_cycle

theorem favored_ne_opposed (excluded : Fin 3) :
    opposedMember excluded ≠ favoredMember excluded := by
  intro same
  have states := congrArg (fun history : model.InformationHistory true (pairSite excluded).1 =>
    history.1.state) same
  change State.asked excluded (excluded + 2) = State.asked excluded (excluded + 1) at states
  have values := congrArg Fin.val (State.asked.inj states).2
  fin_cases excluded <;> norm_num at values

/-- Strict cyclic posterior rankings are impossible for every common Bayes sequence. -/
theorem cyclic_beliefs_inconsistent (assessment : model.BehavioralAssessment)
    (preferences : ∀ excluded,
      (assessment.belief true (pairSite excluded) (opposedMember excluded)).toReal <
        (assessment.belief true (pairSite excluded) (favoredMember excluded)).toReal) :
    ¬ assessment.IsSequentiallyConsistent antichain := by
  intro consistent
  let favorite (index : Fin 3) :=
    (assessment.belief true (pairSite index) (favoredMember index)).toReal
  let opposed (index : Fin 3) :=
    (assessment.belief true (pairSite index) (opposedMember index)).toReal
  have positive (index) : 0 < favorite index :=
    lt_of_le_of_lt ENNReal.toReal_nonneg (preferences index)
  have firstTwo : opposed 0 * opposed 1 ≤ favorite 0 * favorite 1 :=
    mul_le_mul (preferences 0).le (preferences 1).le ENNReal.toReal_nonneg (positive 0).le
  have strict : opposed 0 * opposed 1 * opposed 2 < favorite 0 * favorite 1 * favorite 2 :=
    (mul_le_mul_of_nonneg_right firstTwo ENNReal.toReal_nonneg).trans_lt
      (mul_lt_mul_of_pos_left (preferences 2) (mul_pos (positive 0) (positive 1)))
  have identity := consistent_cycle consistent
  rw [Fin.prod_univ_three, Fin.prod_univ_three] at identity
  exact (ne_of_gt strict) identity

/-- The pure cyclic supports are a special case of the strict-ranking obstruction. -/
theorem concentrated_cyclic_beliefs_inconsistent (assessment : model.BehavioralAssessment)
    (favorites : ∀ excluded,
      assessment.belief true (pairSite excluded) (favoredMember excluded) = 1) :
    ¬ assessment.IsSequentiallyConsistent antichain := by
  apply cyclic_beliefs_inconsistent assessment
  intro excluded
  have zero : assessment.belief true (pairSite excluded) (opposedMember excluded) = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    rw [(PMF.apply_eq_one_iff _ _).mp (favorites excluded)]
    exact favored_ne_opposed excluded
  rw [favorites, zero, ENNReal.toReal_one, ENNReal.toReal_zero]
  norm_num

def mainStrategy (who : Bool) (info : model.InfoState who) : PMF (model.Choice who info) :=
  match info with
  | .idle => PMF.pure ⟨none, rfl⟩
  | .choose => PMF.pure (rootChoice 0)
  | .pair _ => PMF.pure ⟨some 0, ⟨0, rfl⟩⟩

theorem main_rare_zero (actual : Fin 3) :
    mainStrategy false .choose (rootChoice actual.succ) = 0 := by
  apply PMF.pure_apply_of_ne
  intro same
  have actions := congrArg (fun choice : model.Choice false .choose => choice.1) same
  simp [rootChoice] at actions

def observerCyclicBelief : (site : model.InformationSite true) →
    PMF (model.InformationHistory true site.1)
  | ⟨.pair excluded, _⟩ => PMF.pure (favoredMember excluded)
  | site => uniformAssessment.belief true site

def cyclicAssessment : model.BehavioralAssessment where
  strategy := mainStrategy
  belief
    | false, site => uniformAssessment.belief false site
    | true, site => observerCyclicBelief site

theorem cyclic_favorites (excluded : Fin 3) :
    cyclicAssessment.belief true (pairSite excluded) (favoredMember excluded) = 1 := by
  change PMF.pure (favoredMember excluded) (favoredMember excluded) = 1
  exact PMF.pure_apply_self _

theorem cyclic_not_consistent : ¬ cyclicAssessment.IsSequentiallyConsistent antichain :=
  concentrated_cyclic_beliefs_inconsistent cyclicAssessment cyclic_favorites

theorem cyclic_sequentially_rational :
    cyclicAssessment.IsSequentiallyRational bounded.wellFoundedHistories (fun _ _ => 0) :=
  cyclicAssessment.isSequentiallyRational_zero _

/-- Occurrence exponents use the sender's actual own-play record, shared across pairs. -/
def historyExponent (rates : Fin 3 → ℝ) (history : arena.History) : ℝ :=
  ∑ action, (((model.toInfoSignals.ownPlay false history.trace).count
    (.choose, action.succ) : Nat) : ℝ) * rates action

theorem senderRecord (excluded actual : Fin 3) (fits : actual ≠ excluded) :
    model.toInfoSignals.ownPlay false (pairHistory excluded actual fits).trace =
      [(.choose, actual.succ)] := rfl

theorem pair_exponent (rates : Fin 3 → ℝ) (excluded actual : Fin 3)
    (fits : actual ≠ excluded) :
    historyExponent rates (pairHistory excluded actual fits) = rates actual := by
  unfold historyExponent
  rw [senderRecord excluded actual fits]
  simp [List.count_singleton, Prod.mk.injEq, Fin.succ_inj]

/-- The three strict support rows have no shared real exponent vector.
This finite certificate is game-linked through actual behavioral occurrence counts. -/
theorem no_cyclic_history_exponents (rates : Fin 3 → ℝ) :
    ¬ ∀ excluded, historyExponent rates (favoredMember excluded).1 <
      historyExponent rates (opposedMember excluded).1 := by
  simp only [favoredMember, opposedMember, pairMember, pair_exponent]
  intro ordered
  have first := ordered 0
  have second := ordered 1
  have third := ordered 2
  norm_num at first second third
  linarith

end GameTheoryExtensionsTests.CyclicBeliefs
