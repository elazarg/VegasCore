/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensionsTests.CyclicBeliefs
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheory.Protocol.SingleMover
import GameTheory.Protocol.StateKernel
import GameTheoryExtensions.Analysis.Protocol.PowerCertificate

/-! # Unequal tremble orders with nonzero off-path incentives

Nature chooses a pair. An uninformed sender chooses a main action or one of
three rare actions; the observer sees only the pair when the rare action fits.
Terminal states retain the actual sender action and guess for utility evaluation.
-/

noncomputable section

namespace GameTheoryExtensionsTests.UnequalPowerEquilibrium

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Filter

abbrev View := CyclicBeliefs.View

inductive State where
  | initial
  | choosing (excluded : Fin 3)
  | asked (excluded actual : Fin 3)
  | done (action : Fin 4) (guess : Option (Fin 4))
  deriving DecidableEq, Fintype

def State.actor : State → Option Bool
  | .choosing _ => some false
  | .asked .. => some true
  | _ => none

def view (who : Bool) : State → View
  | .choosing _ => if who then .idle else .choose
  | .asked excluded _ => if who then .pair excluded else .idle
  | _ => .idle

abbrev menu := CyclicBeliefs.menu

def advance : State → Option (Fin 4) → PMF State
  | .initial, _ => (PMF.uniformOfFintype (Fin 3)).map State.choosing
  | .choosing excluded, some action =>
      match Fin.cases none some action with
      | none => PMF.pure (.done action none)
      | some actual => PMF.pure
          (if actual = excluded then .done action none else .asked excluded actual)
  | .asked _ actual, guess => PMF.pure (.done actual.succ guess)
  | _, _ => PMF.pure (.done 0 none)

@[reducible] def arena : ExecutionProtocol Bool where
  State := State
  Action _ := Fin 4
  init := .initial
  active state who := state.actor = some who
  available state who := {action | some action ∈ menu (view who state)}
  terminal state := ∃ action guess, state = .done action guess
  step state joint := advance state (joint.1 (state.actor.getD false))
  progress state running := by
    refine ⟨fun who => if state.actor = some who then some 0 else none, ?_⟩
    intro who
    cases state <;> cases who <;> simp_all [State.actor, view, CyclicBeliefs.menu]

@[reducible] def signals : InfoSignals arena where
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

@[reducible] def model : InformationModel arena where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate who state trace choice := by
    rw [info_state]
    cases who <;> cases state <;> cases choice <;>
      simp [LegalOption, State.actor, view, CyclicBeliefs.menu]

instance (who : Bool) : DecidableEq (model.InfoState who) := inferInstanceAs (DecidableEq View)
instance (who : Bool) (info : View) : Fintype (model.Choice who info) := Fintype.ofFinite _
instance (who : Bool) (info : View) : Nonempty (model.Choice who info) := by
  cases info with
  | idle => exact ⟨⟨none, rfl⟩⟩
  | choose => exact ⟨⟨some 0, ⟨0, rfl⟩⟩⟩
  | pair excluded => exact ⟨⟨some 0, ⟨0, rfl⟩⟩⟩

def uniformStrategy (who : Bool) (info : model.InfoState who) : PMF (model.Choice who info) :=
  PMF.uniformOfFintype _

def State.depth : State → Nat
  | .initial => 0
  | .choosing _ => 1
  | .asked .. => 2
  | .done .. => 3

theorem trace_depth {state : arena.State} (trace : arena.Trace state)
    (running : ¬ arena.terminal state) : trace.length = state.depth := by
  refine @Trace.rec Bool arena
    (fun state trace => ¬ arena.terminal state → trace.length = state.depth)
    (fun _ => rfl) ?_ state trace running
  intro source target prior joint legal realized ih running
  cases source with
  | initial =>
      obtain ⟨excluded, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
      simp only [Trace.length, State.depth]
      exact congrArg (· + 1) (ih (by simp))
  | choosing excluded =>
      change target ∈ (advance (.choosing excluded) (joint false)).support at realized
      cases moved : joint false with
      | none =>
          have equal : target = .done 0 none := by simpa [advance, moved] using realized
          exact (running ⟨0, none, equal⟩).elim
      | some action =>
          obtain rfl | ⟨actual, rfl⟩ := Fin.eq_zero_or_eq_succ action
          · have equal : target = .done 0 none := by simpa [advance, moved] using realized
            exact (running ⟨0, none, equal⟩).elim
          · simp only [advance, moved, Fin.cases_succ, PMF.support_pure,
              Set.mem_singleton_iff] at realized
            by_cases same : actual = excluded
            · simp only [same, ↓reduceIte] at realized
              exact (running (by subst target; simp)).elim
            · simp only [same, ↓reduceIte] at realized
              subst target
              simp only [Trace.length, State.depth]
              exact congrArg (· + 1) (ih (by simp))
  | asked excluded actual =>
      have : target = .done actual.succ (joint true) := by
        simpa [advance, State.actor] using realized
      exact (running (by subst target; simp)).elim
  | done action guess => exact (legal.1 (by simp)).elim

theorem bounded : arena.BoundedHorizon 3 := by
  intro state trace long
  by_contra running
  have depth := trace_depth trace running
  cases state <;> simp_all [State.depth]

theorem decision_depth (who : Bool) (site : model.InformationSite who)
    (history : model.InformationHistory who site.1) :
    history.1.trace.length = if who then 2 else 1 := by
  have active : history.1.state.actor = some who := InformationSite.active model site history
  have running : ¬ arena.terminal history.1.state := by
    rintro ⟨action, guess, same⟩
    rw [same] at active
    cases active
  rw [trace_depth history.1.trace running]
  cases state : history.1.state <;> cases who <;> simp_all [State.actor, State.depth]

theorem antichain : model.DecisionInformationAntichain := by
  intro who site first second joint legal reached realized fuel reach
  have monotone := reach.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at monotone
  rw [decision_depth who site first, decision_depth who site second] at monotone
  omega

theorem uniform_full (who : Bool) (site : model.InformationSite who)
    (choice : model.Choice who site.1) : choice ∈ (uniformStrategy who site.1).support :=
  PMF.mem_support_uniformOfFintype choice

private local instance : Finite arena.History :=
  (model.bayesAssessment_isFullyMixed uniformStrategy uniform_full antichain).finite_history
    bounded (fun _ _ => Set.toFinite _) (fun _ => Set.toFinite _)

def rootJoint (action : Fin 4) : Bool → Option (Fin 4)
  | false => some action
  | true => none

theorem rootJoint_legal (excluded : Fin 3) (action : Fin 4) :
    arena.Legal (.choosing excluded) (rootJoint action) := by
  refine ⟨by simp, ?_⟩
  intro who
  cases who <;> simp [arena, State.actor, view, CyclicBeliefs.menu, rootJoint]

theorem initial_legal : arena.Legal .initial arena.noop := by
  exact arena.noop_isLegal (by simp) (by intro who; cases who <;> decide)

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

def senderSite : model.InformationSite false :=
  ⟨.choose, ⟨⟨rootHistory 0, rfl⟩, by simp [arena, rootHistory], 0, ⟨0, rfl⟩⟩⟩

def rootChoice (action : Fin 4) : model.Choice false .choose := ⟨some action, ⟨action, rfl⟩⟩

def guessChoice (excluded : Fin 3) (action : Fin 4) : model.Choice true (.pair excluded) :=
  ⟨some action, ⟨action, rfl⟩⟩

def bestGuess (excluded : Fin 3) : Fin 4 := if excluded = 1 then 1 else 2

def prescribed (who : Bool) (info : model.InfoState who) : PMF (model.Choice who info) :=
  match info with
  | .idle => PMF.pure ⟨none, rfl⟩
  | .choose => PMF.pure ⟨some 0, ⟨0, rfl⟩⟩
  | .pair excluded => PMF.pure ⟨some (bestGuess excluded), ⟨bestGuess excluded, rfl⟩⟩

def reward (who : Bool) : State → ℝ
  | .done action guess => if who then
      if action ≠ 0 ∧ guess = some action then 1 else 0
    else if action = 0 then 1 else 0
  | _ => 0

theorem reward_bounded (who : Bool) (state : State) : |reward who state| ≤ 1 := by
  cases state <;> cases who <;> simp only [reward, Bool.false_eq_true, ↓reduceIte]
  all_goals try split_ifs
  all_goals norm_num

theorem root_history_unique (history : arena.History) (excluded : Fin 3)
    (state : history.state = .choosing excluded) : history = rootHistory excluded := by
  rcases history with ⟨current, trace⟩
  change current = .choosing excluded at state
  have length := trace_depth trace (by rw [state]; simp)
  cases trace with
  | start => cases state
  | @extend source target prior joint legal realized =>
      cases state
      cases prior with
      | start =>
          have idle := arena.eq_noop_of_legal_of_inactive legal
            (by intro who; cases who <;> simp [State.actor])
          subst joint
          rfl
      | extend earlier actions allowed reached =>
          simp only [Trace.length, State.depth] at length
          omega

theorem pair_history_unique (history : arena.History) (excluded actual : Fin 3)
    (state : history.state = .asked excluded actual) :
    ∃ fits : actual ≠ excluded, history = pairHistory excluded actual fits := by
  rcases history with ⟨current, trace⟩
  cases trace with
  | start => cases state
  | @extend source target prior joint legal realized =>
      cases state
      cases source with
      | initial =>
          obtain ⟨index, _, impossible⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
          cases impossible
      | choosing previous =>
          have previousHistory := root_history_unique ⟨_, prior⟩ previous rfl
          have priorEq : prior = rootTrace previous := by
            simpa only [rootHistory, History.mk.injEq, heq_eq_eq, true_and] using previousHistory
          subst prior
          obtain ⟨action, moved⟩ := LegalOption.exists_eq_some_of_active (joint false)
            (arena.legalOption_of_legal legal false) rfl
          have jointEq : joint = rootJoint action := by
            funext who
            cases who with
            | false => exact moved
            | true =>
                exact LegalOption.eq_none_of_inactive _
                  (arena.legalOption_of_legal legal true) (by simp [State.actor])
          subst joint
          obtain rfl | ⟨payload, rfl⟩ := Fin.eq_zero_or_eq_succ action
          · simp [arena, advance, rootJoint, State.actor] at realized
          · change State.asked excluded actual ∈
              (advance (.choosing previous) (some payload.succ)).support at realized
            simp only [advance, Fin.cases_succ, PMF.support_pure,
              Set.mem_singleton_iff] at realized
            by_cases same : payload = previous
            · simp only [same, ↓reduceIte] at realized
              cases realized
            · simp only [same, ↓reduceIte] at realized
              have identities := State.asked.inj realized
              cases identities.1
              cases identities.2
              exact ⟨same, rfl⟩
      | asked previous payload =>
          simp [arena, advance, State.actor] at realized
      | done action guess => exact (legal.1 (by simp)).elim

def rootMember (excluded : Fin 3) : model.InformationHistory false senderSite.1 :=
  ⟨rootHistory excluded, rfl⟩

def pairMember (excluded actual : Fin 3) (fits : actual ≠ excluded) :
    model.InformationHistory true (pairSite excluded).1 := ⟨pairHistory excluded actual fits, rfl⟩

theorem sender_member_eq (history : model.InformationHistory false senderSite.1) :
    ∃ excluded, history = rootMember excluded := by
  rcases history with ⟨⟨state, trace⟩, info⟩
  rw [info_state] at info
  change view false state = .choose at info
  cases state with
  | choosing excluded =>
      refine ⟨excluded, ?_⟩
      apply Subtype.ext
      exact root_history_unique ⟨_, trace⟩ excluded rfl
  | initial => cases info
  | asked excluded actual => cases info
  | done action guess => cases info

theorem observer_member_eq (excluded : Fin 3)
    (history : model.InformationHistory true (pairSite excluded).1) :
    ∃ (actual : Fin 3) (fits : actual ≠ excluded), history = pairMember excluded actual fits := by
  rcases history with ⟨⟨state, trace⟩, info⟩
  rw [info_state] at info
  change view true state = .pair excluded at info
  cases state with
  | asked previous actual =>
      cases CyclicBeliefs.View.pair.inj info
      obtain ⟨fits, same⟩ := pair_history_unique ⟨_, trace⟩ excluded actual rfl
      refine ⟨actual, fits, ?_⟩
      apply Subtype.ext
      exact same
  | initial => cases info
  | choosing previous => cases info
  | done action guess => cases info

theorem sender_site_unique (site : model.InformationSite false) : site = senderSite := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationSite.active model site history
  have info := history.2
  rw [info_state] at info
  cases state : history.1.state with
  | choosing excluded =>
      apply Subtype.ext
      change site.1 = .choose
      simpa only [state, view, Bool.false_eq_true, ↓reduceIte] using info.symm
  | initial => simp [state, State.actor] at active
  | asked excluded actual => simp [state, State.actor] at active
  | done action guess => simp [state, State.actor] at active

theorem observer_site_eq (site : model.InformationSite true) :
    ∃ excluded, site = pairSite excluded := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationSite.active model site history
  have info := history.2
  rw [info_state] at info
  cases state : history.1.state with
  | asked excluded actual =>
      refine ⟨excluded, Subtype.ext ?_⟩
      change site.1 = .pair excluded
      simpa only [state, view, ↓reduceIte] using info.symm
  | initial => simp [state, State.actor] at active
  | choosing excluded => simp [state, State.actor] at active
  | done action guess => simp [state, State.actor] at active

def firstWeight (excluded : Fin 3) : ℝ :=
  if excluded = 0 then 1 else if excluded = 1 then 0 else 1 / 3

theorem firstWeight_nonnegative (excluded : Fin 3) : 0 ≤ firstWeight excluded := by
  fin_cases excluded <;> norm_num [firstWeight]

theorem firstWeight_le_one (excluded : Fin 3) : firstWeight excluded ≤ 1 := by
  fin_cases excluded <;> norm_num [firstWeight]

def firstMember (excluded : Fin 3) : model.InformationHistory true (pairSite excluded).1 :=
  pairMember excluded (excluded + 1) (by fin_cases excluded <;> decide)

def secondMember (excluded : Fin 3) : model.InformationHistory true (pairSite excluded).1 :=
  pairMember excluded (excluded + 2) (by fin_cases excluded <;> decide)

def pairBelief (excluded : Fin 3) : PMF (model.InformationHistory true (pairSite excluded).1) :=
  mix (firstWeight excluded) (firstWeight_nonnegative excluded) (firstWeight_le_one excluded)
    (PMF.pure (firstMember excluded)) (PMF.pure (secondMember excluded))

def assessment : model.BehavioralAssessment where
  strategy := prescribed
  belief
    | false, ⟨.choose, _⟩ => (PMF.uniformOfFintype (Fin 3)).map rootMember
    | true, ⟨.pair excluded, _⟩ => pairBelief excluded
    | _, site => PMF.pure (Classical.choose site.2)

def coefficient (who : Bool) (info : model.InfoState who) (choice : model.Choice who info) : ℝ :=
  match info with
  | .choose => if choice.val = some 3 then 4 else if choice.val = some 2 then 2 else 1
  | _ => 1

def order (who : Bool) (info : model.InfoState who) (choice : model.Choice who info) : Nat :=
  match info with
  | .idle => 0
  | .choose => if choice.val = some 0 then 0 else if choice.val = some 3 then 2 else 1
  | .pair excluded => if choice.val = some (bestGuess excluded) then 0 else 1

theorem coefficient_positive (who : Bool) (info : model.InfoState who)
    (choice : model.Choice who info) : 0 < coefficient who info choice := by
  unfold coefficient
  split <;> (try split) <;> (try split) <;> norm_num

theorem constantTerm (who : Bool) (info : model.InfoState who) (choice : model.Choice who info) :
    (if order who info choice = 0 then coefficient who info choice else 0) =
      (prescribed who info choice).toReal := by
  classical
  cases info with
  | idle =>
      rcases choice with ⟨value, allowed⟩
      change value = none at allowed
      subst value
      norm_num [order, coefficient, prescribed, PMF.pure_apply]
  | choose =>
      rcases choice with ⟨value, ⟨action, rfl⟩⟩
      fin_cases action <;> norm_num [order, coefficient, prescribed, PMF.pure_apply]
  | pair excluded =>
      rcases choice with ⟨value, ⟨action, rfl⟩⟩
      by_cases same : action = bestGuess excluded
      · subst action
        norm_num [order, coefficient, prescribed, PMF.pure_apply]
      · norm_num [order, coefficient, prescribed, PMF.pure_apply, same]

def preferredActual (excluded : Fin 3) : Fin 3 := if excluded = 1 then 0 else 1

theorem preferredActual_fits (excluded : Fin 3) : preferredActual excluded ≠ excluded := by
  fin_cases excluded <;> decide

def reference : (who : Bool) → (site : model.InformationSite who) →
    model.InformationHistory who site.1
  | false, ⟨.choose, _⟩ => rootMember 0
  | true, ⟨.pair excluded, _⟩ =>
      pairMember excluded (preferredActual excluded) (preferredActual_fits excluded)
  | _, site => Classical.choose site.2

theorem rootMember_injective : Function.Injective rootMember := by
  intro first second same
  have states := congrArg (fun history : model.InformationHistory false senderSite.1 =>
    history.1.state) same
  exact State.choosing.inj states

theorem pairMember_eq_iff (excluded actual other : Fin 3)
    (fits : actual ≠ excluded) (otherFits : other ≠ excluded) :
    pairMember excluded actual fits = pairMember excluded other otherFits ↔ actual = other := by
  constructor
  · intro same
    have states := congrArg (fun history : model.InformationHistory true (pairSite excluded).1 =>
      history.1.state) same
    exact (State.asked.inj states).2
  · intro same
    subst other
    rfl

theorem sender_belief (excluded : Fin 3) :
    (assessment.belief false senderSite (rootMember excluded)).toReal = 1 / 3 := by
  change (((PMF.uniformOfFintype (Fin 3)).map rootMember) (rootMember excluded)).toReal = _
  rw [pmf_map_apply_of_injective _ rootMember_injective, PMF.uniformOfFintype_apply]
  norm_num

theorem observer_belief (excluded actual : Fin 3) (fits : actual ≠ excluded) :
    (assessment.belief true (pairSite excluded) (pairMember excluded actual fits)).toReal =
      firstWeight excluded * (if actual = excluded + 1 then 1 else 0) +
        (1 - firstWeight excluded) * (if actual = excluded + 2 then 1 else 0) := by
  change (pairBelief excluded (pairMember excluded actual fits)).toReal = _
  rw [pairBelief, mix_apply_toReal]
  simp only [firstMember, secondMember, PMF.pure_apply, pairMember_eq_iff]
  split_ifs <;> norm_num

def rareCoefficient (actual : Fin 3) : ℝ := if actual = 2 then 4 else if actual = 1 then 2 else 1

def rareOrder (actual : Fin 3) : Nat := if actual = 2 then 2 else 1

theorem root_order (excluded : Fin 3) : model.powerHistoryOrder order (rootTrace excluded) = 0 := by
  simp only [rootTrace, powerHistoryOrder, Fintype.sum_bool]
  change 0 + (0 + 0) = 0
  rfl

theorem root_coefficient (excluded : Fin 3) :
    model.powerHistoryCoefficient coefficient (rootTrace excluded) = 1 / 3 := by
  simp only [rootTrace, powerHistoryCoefficient, Fintype.prod_bool]
  change 1 * ((1 * 1) *
    (((PMF.uniformOfFintype (Fin 3)).map State.choosing) (.choosing excluded)).toReal) = _
  rw [pmf_map_apply_of_injective _ (fun _ _ same => State.choosing.inj same),
    PMF.uniformOfFintype_apply]
  norm_num

theorem rare_order (actual : Fin 3) :
    order false .choose (rootChoice actual.succ) = rareOrder actual := by
  fin_cases actual <;> rfl

theorem rare_coefficient (actual : Fin 3) :
    coefficient false .choose (rootChoice actual.succ) = rareCoefficient actual := by
  fin_cases actual <;> rfl

theorem pair_order (excluded actual : Fin 3) (fits : actual ≠ excluded) :
    model.powerHistoryOrder order (pairTrace excluded actual fits) = rareOrder actual := by
  simp only [pairTrace, powerHistoryOrder, root_order, Fintype.sum_bool]
  change 0 + (0 + order false .choose (rootChoice actual.succ)) = _
  rw [rare_order]
  simp only [Nat.zero_add]

theorem pair_coefficient (excluded actual : Fin 3) (fits : actual ≠ excluded) :
    model.powerHistoryCoefficient coefficient (pairTrace excluded actual fits) =
      (1 / 3) * rareCoefficient actual := by
  simp only [pairTrace, powerHistoryCoefficient, root_coefficient, Fintype.prod_bool]
  change (1 / 3) * ((1 * coefficient false .choose (rootChoice actual.succ)) *
    ((advance (.choosing excluded) (some actual.succ)) (.asked excluded actual)).toReal) = _
  simp only [advance, Fin.cases_succ, fits, ↓reduceIte, PMF.pure_apply_self,
    ENNReal.toReal_one, rare_coefficient]
  ring

def rootChoiceEquiv : Fin 4 ≃ model.Choice false .choose :=
  Equiv.ofBijective rootChoice ⟨fun _ _ same => Option.some.inj (congrArg Subtype.val same),
    fun choice => by
      obtain ⟨action, same⟩ := choice.property
      exact ⟨action, Subtype.ext same.symm⟩⟩

theorem senderNormalizer (t : ℝ) :
    powerNormalizer (coefficient false .choose) (order false .choose) t =
      1 + 3 * t + 4 * t ^ 2 := by
  rw [powerNormalizer, ← Equiv.sum_comp rootChoiceEquiv]
  rw [Fin.sum_univ_four]
  change 1 * t ^ 0 + 1 * t ^ 1 + 2 * t ^ 1 + 4 * t ^ 2 = _
  ring

/-- Actual normalized sender probabilities, not just abstract monomial labels. -/
theorem sender_power_formula (t : ℝ) (positive : 0 < t) (action : Fin 4) :
    ((model.powerProfile prescribed coefficient coefficient_positive order t positive)
      false .choose (rootChoice action)).toReal =
        (if action = 0 then 1 else if action = 1 then t else
          if action = 2 then 2 * t else 4 * t ^ 2) / (1 + 3 * t + 4 * t ^ 2) := by
  change (normalizedPower (coefficient false .choose) (coefficient_positive false .choose)
    (order false .choose) t positive (rootChoice action)).toReal = _
  rw [normalizedPower_toReal, senderNormalizer]
  fin_cases action
  · change 1 * t ^ 0 / (1 + 3 * t + 4 * t ^ 2) = 1 / (1 + 3 * t + 4 * t ^ 2)
    simp only [pow_zero, mul_one]
  · change 1 * t ^ 1 / (1 + 3 * t + 4 * t ^ 2) = t / (1 + 3 * t + 4 * t ^ 2)
    simp only [pow_one, one_mul]
  · change 2 * t ^ 1 / (1 + 3 * t + 4 * t ^ 2) = 2 * t / (1 + 3 * t + 4 * t ^ 2)
    rw [pow_one]
  · rfl

theorem reference_sender : reference false senderSite = rootMember 0 := rfl

theorem reference_observer (excluded : Fin 3) :
    reference true (pairSite excluded) =
      pairMember excluded (preferredActual excluded) (preferredActual_fits excluded) := rfl

theorem minimal (who : Bool) (site : model.InformationSite who)
    (history : model.InformationHistory who site.1) :
    model.powerHistoryOrder order (reference who site).1.trace ≤
      model.powerHistoryOrder order history.1.trace := by
  cases who with
  | false =>
      cases sender_site_unique site
      obtain ⟨excluded, rfl⟩ := sender_member_eq history
      simp only [reference_sender, rootMember, rootHistory, root_order, le_refl]
  | true =>
      obtain ⟨excluded, rfl⟩ := observer_site_eq site
      obtain ⟨actual, fits, rfl⟩ := observer_member_eq excluded history
      simp only [reference_observer, pairMember, pairHistory, pair_order]
      fin_cases excluded <;> fin_cases actual <;> norm_num [preferredActual, rareOrder] at *

theorem certificate_support (who : Bool) (site : model.InformationSite who)
    (history : model.InformationHistory who site.1) :
    model.powerHistoryOrder order history.1.trace =
        model.powerHistoryOrder order (reference who site).1.trace ↔
      (assessment.belief who site history).toReal ≠ 0 := by
  cases who with
  | false =>
      cases sender_site_unique site
      obtain ⟨excluded, rfl⟩ := sender_member_eq history
      rw [sender_belief, reference_sender]
      simp only [rootMember, rootHistory, root_order]
      norm_num
  | true =>
      obtain ⟨excluded, rfl⟩ := observer_site_eq site
      obtain ⟨actual, fits, rfl⟩ := observer_member_eq excluded history
      rw [observer_belief, reference_observer]
      simp only [pairMember, pairHistory, pair_order]
      fin_cases excluded <;> fin_cases actual <;>
        norm_num [preferredActual, rareOrder, firstWeight] at *

theorem certificate_ratios (who : Bool) (site : model.InformationSite who)
    (history : model.InformationHistory who site.1)
    (positive : (assessment.belief who site history).toReal ≠ 0) :
    model.powerHistoryCoefficient coefficient history.1.trace /
        model.powerHistoryCoefficient coefficient (reference who site).1.trace =
      (assessment.belief who site history).toReal /
        (assessment.belief who site (reference who site)).toReal := by
  cases who with
  | false =>
      cases sender_site_unique site
      obtain ⟨excluded, rfl⟩ := sender_member_eq history
      rw [sender_belief, reference_sender, sender_belief]
      simp only [rootMember, rootHistory, root_coefficient]
  | true =>
      obtain ⟨excluded, rfl⟩ := observer_site_eq site
      obtain ⟨actual, fits, rfl⟩ := observer_member_eq excluded history
      rw [observer_belief] at positive
      rw [observer_belief, reference_observer, observer_belief]
      simp only [pairMember, pairHistory, pair_coefficient]
      fin_cases excluded <;> fin_cases actual <;>
        norm_num [preferredActual, rareCoefficient, firstWeight] at *

/-- The three prescribed pair beliefs are exactly (1/3,2/3), (1,0), (0,1)
in the listed action orders (a,b), (b,c), and (c,a). -/
theorem specified_pair_beliefs :
    ((assessment.belief true (pairSite 2) (pairMember 2 0 (by decide))).toReal,
      (assessment.belief true (pairSite 2) (pairMember 2 1 (by decide))).toReal) =
        ((1 / 3 : ℝ), (2 / 3 : ℝ)) ∧
    ((assessment.belief true (pairSite 0) (pairMember 0 1 (by decide))).toReal,
      (assessment.belief true (pairSite 0) (pairMember 0 2 (by decide))).toReal) = (1, 0) ∧
    ((assessment.belief true (pairSite 1) (pairMember 1 2 (by decide))).toReal,
      (assessment.belief true (pairSite 1) (pairMember 1 0 (by decide))).toReal) = (0, 1) := by
  simp only [observer_belief]
  norm_num [firstWeight]

/-- One explicit common power sequence realizes this exact complete assessment,
including all zero-probability histories in its off-path information fibers. -/
theorem consistent : assessment.IsSequentiallyConsistent antichain :=
  model.powerCertificate_consistent assessment coefficient coefficient_positive order constantTerm
    reference minimal certificate_support certificate_ratios antichain

theorem single (state : State) {first second : Bool} :
    arena.active state first → arena.active state second → first = second := by
  intro firstActs secondActs
  exact Option.some.inj (firstActs.symm.trans secondActs)

def kernel (profile : ∀ who, model.BehavioralPolicy who) : State → PMF State
  | .initial => (PMF.uniformOfFintype (Fin 3)).map State.choosing
  | .choosing excluded => (profile false .choose).bind fun choice =>
      advance (.choosing excluded) choice.val
  | .asked excluded actual => (profile true (.pair excluded)).bind fun choice =>
      advance (.asked excluded actual) choice.val
  | .done action guess => PMF.pure (.done action guess)

theorem chooser_kernel (profile : ∀ who, model.BehavioralPolicy who)
    (history : arena.History) (running : ¬ arena.terminal history.state) :
    (model.singleMoverChooser single profile history running).bind
      (arena.step history.state) = kernel profile history.state := by
  have sourceMarginal := model.singleMoverJoint_marginal single profile history running false
  have observerMarginal := model.singleMoverJoint_marginal single profile history running true
  rw [info_state] at sourceMarginal observerMarginal
  rcases history with ⟨current, trace⟩
  cases current with
  | initial =>
      change (_ : PMF _).bind (fun _ => (PMF.uniformOfFintype (Fin 3)).map State.choosing) = _
      exact PMF.bind_const _ _
  | choosing excluded =>
      have compared := congrArg
        (fun law : PMF (Option (Fin 4)) => law.bind (advance (.choosing excluded))) sourceMarginal
      simpa [singleMoverChooser, PMF.bind_map, arena, State.actor, view, kernel,
        Function.comp_def] using compared
  | asked excluded actual =>
      have compared := congrArg
        (fun law : PMF (Option (Fin 4)) => law.bind (advance (.asked excluded actual)))
          observerMarginal
      simpa [singleMoverChooser, PMF.bind_map, arena, State.actor, view, kernel,
        Function.comp_def] using compared
  | done action guess => exact (running (by simp)).elim

theorem run_states (profile : ∀ who, model.BehavioralPolicy who) (fuel : Nat)
    (history : arena.History) :
    ((model.runBehavioralFrom profile fuel history).map History.state) =
      (fun law => law.bind (kernel profile))^[fuel] (PMF.pure history.state) := by
  rw [← model.runSingleMoverBehavioralFrom_eq_runBehavioralFrom single]
  apply runRandomizedFor_map_state
  · rintro state ⟨action, guess, rfl⟩
    rfl
  · exact chooser_kernel profile

theorem kernel_after_observer (profile : ∀ who, model.BehavioralPolicy who)
    (excluded actual : Fin 3) :
    (kernel profile (.asked excluded actual)).bind (kernel profile) =
      kernel profile (.asked excluded actual) := by
  simp only [kernel, PMF.bind_bind, advance, PMF.pure_bind]

theorem terminal_observer_value (profile : ∀ who, model.BehavioralPolicy who)
    (history : arena.History) (excluded actual : Fin 3)
    (state : history.state = .asked excluded actual) :
    expect (model.runBehavioralTerminalFrom bounded.wellFoundedHistories profile history)
        (fun final => reward true final.state) =
      expect (profile true (.pair excluded))
        (fun choice => if choice.val = some actual.succ then (1 : ℝ) else 0) := by
  rw [model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _ bounded]
  have projected := congrArg (fun law => expect law (reward true)) (run_states profile 3 history)
  rw [expect_map, Function.comp_def, state] at projected
  rw [show 3 = 2 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_zero_apply,
    PMF.pure_bind, kernel_after_observer, kernel_after_observer] at projected
  rw [projected, kernel, expect_bind_of_finite]
  apply expect_congr_on_support
  intro choice _
  rw [advance, expect_pure]
  have rare : actual.succ ≠ (0 : Fin 4) := Fin.succ_ne_zero actual
  change (if actual.succ ≠ 0 ∧ choice.val = some actual.succ then (1 : ℝ) else 0) = _
  by_cases correct : choice.val = some actual.succ
  · rw [ite_eq_left ⟨rare, correct⟩, ite_eq_left correct]
  · rw [ite_eq_right (fun both => correct both.2), ite_eq_right correct]

theorem terminal_main_value (history : arena.History) (excluded : Fin 3)
    (state : history.state = .choosing excluded) :
    expect (model.runBehavioralTerminalFrom bounded.wellFoundedHistories prescribed history)
      (fun final => reward false final.state) = 1 := by
  rw [model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _ bounded]
  have projected := congrArg (fun law => expect law (reward false))
    (run_states prescribed 3 history)
  rw [expect_map, Function.comp_def, state] at projected
  rw [projected]
  norm_num [Function.iterate_succ_apply', kernel, prescribed, advance, reward, expect_pure]

def guessValue (excluded : Fin 3) (choice : model.Choice true (.pair excluded)) : ℝ :=
  firstWeight excluded * (if choice.val = some (excluded + 1).succ then 1 else 0) +
    (1 - firstWeight excluded) * (if choice.val = some (excluded + 2).succ then 1 else 0)

def observerValue (excluded : Fin 3) : ℝ := if excluded = 2 then 2 / 3 else 1

theorem guessValue_le (excluded : Fin 3) (choice : model.Choice true (.pair excluded)) :
    guessValue excluded choice ≤ observerValue excluded := by
  rcases choice with ⟨value, ⟨action, rfl⟩⟩
  fin_cases excluded <;> fin_cases action <;>
    norm_num [guessValue, firstWeight, observerValue]

theorem guessValue_best (excluded : Fin 3) :
    guessValue excluded (guessChoice excluded (bestGuess excluded)) = observerValue excluded := by
  fin_cases excluded <;> norm_num [guessValue, firstWeight, observerValue, guessChoice, bestGuess]
  decide

/-- Each observer prescription is strictly best against every other pure legal
choice, including the fourth choice which guesses no rare sender action. -/
theorem guessValue_strict (excluded : Fin 3) (choice : model.Choice true (.pair excluded))
    (different : choice.val ≠ some (bestGuess excluded)) :
    guessValue excluded choice < observerValue excluded := by
  rcases choice with ⟨value, ⟨action, rfl⟩⟩
  fin_cases excluded <;> fin_cases action <;>
    norm_num [guessValue, firstWeight, observerValue, bestGuess] at *

theorem observer_context_value (excluded : Fin 3) (alternative : model.BehavioralPolicy true) :
    (assessment.continuationContext bounded.wellFoundedHistories (pairSite excluded)
      (fun history => reward true history.state)).value alternative =
        expect (alternative (.pair excluded)) (guessValue excluded) := by
  rw [BehavioralAssessment.continuationContext_value,
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  have future (actual : Fin 3) (fits : actual ≠ excluded) :
      expect (model.runBehavioralTerminalFrom bounded.wellFoundedHistories
          (Profile.update (sig := model.behavioralSignature) assessment.strategy true alternative)
          (pairHistory excluded actual fits)) (fun final => reward true final.state) =
        expect (alternative (.pair excluded))
          (fun choice => if choice.val = some actual.succ then (1 : ℝ) else 0) := by
    rw [terminal_observer_value _ _ excluded actual rfl, Profile.update_same]
  change expect (pairBelief excluded) _ = _
  rw [pairBelief, expect_mix_of_finite, expect_pure, expect_pure]
  dsimp only [firstMember, secondMember, pairMember]
  rw [future (excluded + 1) (by fin_cases excluded <;> decide),
    future (excluded + 2) (by fin_cases excluded <;> decide)]
  rw [show guessValue excluded = fun choice =>
      firstWeight excluded * (if choice.val = some (excluded + 1).succ then 1 else 0) +
      (1 - firstWeight excluded) * (if choice.val = some (excluded + 2).succ then 1 else 0)
      from rfl,
    expect_add (payoffIntegrable_const_mul (payoffIntegrable_of_finite _ _))
      (payoffIntegrable_const_mul (payoffIntegrable_of_finite _ _)), expect_const_mul,
    expect_const_mul]

theorem sender_context_main :
    (assessment.continuationContext bounded.wellFoundedHistories senderSite
      (fun history => reward false history.state)).value (assessment.strategy false) = 1 := by
  rw [BehavioralAssessment.continuationContext_value, Profile.update_eq_self,
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  change expect ((PMF.uniformOfFintype (Fin 3)).map rootMember) _ = _
  rw [expect_map]
  change expect (PMF.uniformOfFintype (Fin 3)) (fun excluded =>
    expect (model.runBehavioralTerminalFrom bounded.wellFoundedHistories prescribed
      (rootHistory excluded)) (fun final => reward false final.state)) = 1
  exact (expect_congr_on_support (fun excluded _ =>
    terminal_main_value (rootHistory excluded) excluded rfl)).trans (expect_constant _ _)

/-- All whole-policy deviations are evaluated by the original terminal contexts.
The sender obtains the global upper payoff one; each observer's belief selects
its strict best guess. -/
theorem sequentially_rational :
    assessment.IsSequentiallyRational bounded.wellFoundedHistories
      (fun who history => reward who history.state) := by
  intro who site
  apply (Context.isLocallyOptimal_iff_of_integrable
    (ctx := assessment.continuationContext bounded.wellFoundedHistories site
      (fun history => reward who history.state))
    (payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)).mpr
  intro alternative _
  cases who with
  | false =>
      cases sender_site_unique site
      rw [sender_context_main, BehavioralAssessment.continuationContext_value]
      apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1
      intro final _
      exact (abs_le.mp (reward_bounded false final.state)).2
  | true =>
      obtain ⟨excluded, rfl⟩ := observer_site_eq site
      rw [observer_context_value, observer_context_value]
      change expect (alternative (.pair excluded)) (guessValue excluded) ≤
        expect (PMF.pure (guessChoice excluded (bestGuess excluded))) (guessValue excluded)
      rw [expect_pure, guessValue_best]
      exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
        (fun choice _ => guessValue_le excluded choice)

/-- Unequal-order power consistency and genuine off-path incentives hold for
one exact prescribed complete assessment, giving actual sequential equilibrium. -/
theorem sequential_equilibrium :
    assessment.IsSequentialEquilibrium antichain bounded.wellFoundedHistories
      (fun who history => reward who history.state) := ⟨sequentially_rational, consistent⟩

/-- The initialized equilibrium preserves the entire joint terminal readout and
both realized utilities, not only their separate expectations. -/
theorem initialized_joint_law :
    (model.runBehavioralTerminalFrom bounded.wellFoundedHistories assessment.strategy
      arena.initHistory).map (fun final =>
        (final.state, reward false final.state, reward true final.state)) =
      PMF.pure (State.done 0 none, (1 : ℝ), (0 : ℝ)) := by
  have completes (excluded : Fin 3) :
      kernel prescribed (.choosing excluded) = PMF.pure (.done 0 none) := by
    simp only [kernel, prescribed, PMF.pure_bind, advance, Fin.cases_zero]
  have states :
      (model.runBehavioralTerminalFrom bounded.wellFoundedHistories assessment.strategy
        arena.initHistory).map History.state = PMF.pure (.done 0 none) := by
    rw [model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _ bounded, run_states]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind]
    change (((PMF.uniformOfFintype (Fin 3)).map State.choosing).bind
      (kernel prescribed)).bind (kernel prescribed) = _
    rw [PMF.bind_map]
    simp only [Function.comp_def]
    simp_rw [completes]
    rw [PMF.bind_const, PMF.pure_bind]
    rfl
  calc
    _ = ((model.runBehavioralTerminalFrom bounded.wellFoundedHistories assessment.strategy
        arena.initHistory).map History.state).map
          (fun state => (state, reward false state, reward true state)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [states, PMF.pure_map]
      rfl

theorem sender_strict_main (actual : Fin 3) (guess : Option (Fin 4)) :
    reward false (.done 0 none) = 1 ∧ reward false (.done actual.succ guess) = 0 := by
  constructor
  · norm_num [reward]
  · change (if actual.succ = 0 then (1 : ℝ) else 0) = 0
    exact ite_eq_right (Fin.succ_ne_zero actual)

end GameTheoryExtensionsTests.UnequalPowerEquilibrium
