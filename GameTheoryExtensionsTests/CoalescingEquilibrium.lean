/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion
import GameTheory.Protocol.SingleMover
import GameTheory.Protocol.StateKernel
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Coalescing distinguishes outcome implementation from a fixed compiler

One player chooses `x`, `ya`, or `yb` in the coalesced game. The split game
first offers `x` or `y`, then offers `a` or `b` after `y`. Both utilities reward
`x` by two; they reward opposite continuations after `y` by one.

The same source assessment is sequentially optimal for both utilities. Each
utility separately has a native sequential equilibrium with outcome `x`, but
no single native strategy is sequentially rational for both, even with different
beliefs. This concerns a utility-independent compiler; a compiler allowed to
inspect utilities can choose the appropriate off-path continuation.
-/

noncomputable section

namespace GameTheoryExtensionsTests.CoalescingEquilibrium

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

abbrev Outcome := Option Bool
abbrev State := List Outcome

@[reducible] def active (split : Bool) (state : State) : Prop :=
  state = [] ∨ split = true ∧ state = [some false]

@[reducible] def available (split : Bool) (state : State) (action : Outcome) : Prop :=
  if state = [] then split = false ∨ action ≠ some true else action.isSome = true

@[reducible] def arena (split : Bool) : ExecutionProtocol Unit where
  State := State
  Action _ := Outcome
  init := []
  active state _ := active split state
  available state _ := {action | available split state action}
  terminal state := ¬ active split state
  step state joint := PMF.pure ((joint.1 ()).getD none :: state)
  progress state running := by
    refine ⟨fun _ => some (if state = [] then none else some false), fun _ => ?_⟩
    refine ⟨not_not.mp running, ?_⟩
    by_cases empty : state = [] <;> simp [available, empty]

@[reducible] def signals (split : Bool) : InfoSignals (arena split) where
  PublicSignal := Unit
  PrivateSignal _ := State
  initialPublic := ()
  initialPrivate _ := []
  publicSignal _ := ()
  privateSignal _ event := event.target
  InfoState _ := State
  initInfo _ secret _ := secret
  pushInfo _ _ _ secret _ := secret

@[simp] theorem info_state (split : Bool) : ∀ {state : State}
    (trace : (arena split).Trace state), (signals split).infoOf () trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def model (split : Bool) : InformationModel (arena split) where
  toInfoSignals := signals split
  menu _ state := {choice | match choice with
    | some action => active split state ∧ available split state action
    | none => ¬ active split state}
  menu_adequate := by
    intro who state trace choice
    cases who
    rw [info_state]
    cases choice <;> rfl

theorem history_length (split : Bool) : ∀ {state : State} (trace : (arena split).Trace state),
    trace.length = state.length
  | _, .start => rfl
  | _, .extend prior _ _ realized => by
      cases (PMF.mem_support_pure_iff _ _).mp realized
      simpa only [Trace.length, List.length_cons] using
        congrArg (· + 1) (history_length split prior)

theorem bounded (split : Bool) : (arena split).BoundedHorizon 2 := by
  intro state trace enough
  rw [history_length] at enough
  change ¬ active split state
  rintro (rfl | ⟨_, rfl⟩) <;> simp_all

def canonical (split goal : Bool) : Profile (model split).behavioralSignature := fun _ state =>
  if running : active split state then
    PMF.pure ⟨some (if state = [] then none else some goal), by
      refine ⟨running, ?_⟩
      by_cases empty : state = [] <;> simp [available, empty]⟩
  else PMF.pure ⟨none, running⟩

instance (split : Bool) (who : Unit) (state : State) :
    Fintype ((model split).Choice who state) := by
  classical
  exact Fintype.ofFinite _

instance (split : Bool) (who : Unit) (state : State) :
    Nonempty ((model split).Choice who state) :=
  ⟨((canonical split false) who state).support_nonempty.choose⟩

def reference (split : Bool) : (model split).BehavioralAssessment :=
  .ofStrategy (fun _ _ => (PMF.uniformOfFintype _))

theorem reference_mixed (split : Bool) : (reference split).IsFullyMixed := by
  intro who site choice
  exact PMF.mem_support_uniformOfFintype choice

instance (split : Bool) : Finite (arena split).History :=
  (reference_mixed split).finite_history (bounded split) (fun _ _ => Set.toFinite _)
    (fun _ => by simp)

instance (split : Bool) : Fintype (arena split).History := Fintype.ofFinite _

instance (split : Bool) (who : Unit) (site : (model split).InformationSite who) :
    Fintype ((model split).InformationHistory who site.1) := by
  classical
  infer_instance

theorem antichain (split : Bool) : (model split).DecisionInformationAntichain := by
  intro who site first second joint legal target realized fuel reached
  cases who
  have firstState : first.1.state = site.1 := by simpa using first.2
  have secondState : second.1.state = site.1 := by simpa using second.2
  have increases := reached.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at increases
  rw [history_length, history_length, firstState, secondState] at increases
  omega

def kernel {split : Bool} (profile : Profile (model split).behavioralSignature)
    (state : State) : PMF State :=
  if active split state then
    (profile () state).map (fun choice => choice.val.getD none :: state)
  else PMF.pure state

theorem single (split : Bool) : ∀ state {first second},
    (arena split).active state first → (arena split).active state second → first = second := by
  intros
  exact Subsingleton.elim _ _

theorem chooser_kernel {split : Bool} (profile : Profile (model split).behavioralSignature)
    (history : (arena split).History) (running : ¬ (arena split).terminal history.state) :
    ((model split).singleMoverChooser (single split) profile history running).bind
      ((arena split).step history.state) = kernel profile history.state := by
  have marginal := (model split).singleMoverJoint_marginal (single split)
    profile history running ()
  rw [info_state] at marginal
  have mapped := congrArg (fun law => law.map
    (fun choice : Option Outcome => choice.getD none :: history.state)) marginal
  have acts : active split history.state := not_not.mp running
  simpa only [InformationModel.singleMoverChooser, arena, kernel, acts, ite_eq_left,
    PMF.map_comp, Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind,
    PMF.pure_bind] using mapped

theorem run_states {split : Bool} (profile : Profile (model split).behavioralSignature)
    (fuel : Nat) (history : (arena split).History) :
    ((model split).runBehavioralFrom profile fuel history).map History.state =
      (fun law => law.bind (kernel profile))^[fuel] (PMF.pure history.state) := by
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    (model split) (single split)]
  apply runRandomizedFor_map_state
  · intro state stopped
    exact ite_eq_right stopped
  · exact chooser_kernel profile

def reward (goal : Bool) (state : State) : ℝ :=
  if state = [none] then 2 else if state.headD none = some goal then 1 else 0

def utility (goal : Bool) (outcome : Outcome) : ℝ :=
  if outcome = none then 2 else if outcome = some goal then 1 else 0

/-- Both games use the same utility on their three public outcomes. The extra
record retained by the split presentation has no payoff significance. -/
theorem terminal_reward (split goal : Bool) (history : (arena split).History)
    (stopped : (arena split).terminal history.state) :
    reward goal history.state = utility goal (history.state.headD none) := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start => exact (stopped (Or.inl rfl)).elim
  | @extend before target prior joint legal realized =>
      have acts : active split before := not_not.mp legal.1
      obtain ⟨action, selected⟩ := LegalOption.exists_eq_some_of_active
        (E := arena split) (joint ()) ((arena split).legalOption_of_legal legal ()) acts
      have permitted : available split before action := by
        have authorized := (arena split).legalOption_of_legal legal ()
        rw [selected] at authorized
        exact authorized.2
      have next : state = action :: before := by
        simpa only [arena, selected, Option.getD_some] using
          (PMF.mem_support_pure_iff _ _).mp realized
      subst state
      cases action with
      | none =>
          have empty : before = [] := by
            by_contra nonempty
            simp [available, nonempty] at permitted
          subst before
          simp [reward, utility]
      | some bit => simp [reward, utility]

theorem reward_le_two (goal : Bool) (state : State) : reward goal state ≤ 2 := by
  unfold reward
  split <;> norm_num
  split <;> norm_num

/-- Rewards are bounded, so every law over states integrates them. -/
theorem reward_integrable (goal : Bool) (law : PMF State) : PayoffIntegrable law (reward goal) :=
  payoffIntegrable_of_bounded _ _ (C := 2) fun state => by
    unfold reward
    split_ifs <;> norm_num

theorem canonical_source (goal : Bool) : canonical false goal = canonical false false := by
  funext who state
  by_cases empty : state = []
  · subst state; simp [canonical, active]
  · simp [canonical, active, empty]

theorem canonical_root_law (split goal : Bool) :
    ((model split).runBehavioral (canonical split goal) 2).map History.state =
      PMF.pure [none] := by
  rw [InformationModel.runBehavioral, run_states]
  simp [Function.iterate_succ_apply', kernel, canonical, active,
    initHistory, PMF.pure_bind]

theorem canonical_branch_law (goal : Bool) (history : (arena true).History)
    (atBranch : history.state = [some false]) :
    ((model true).runBehavioralFrom (canonical true goal) 2 history).map History.state =
      PMF.pure [some goal, some false] := by
  rw [run_states, atBranch]
  simp [Function.iterate_succ_apply', kernel, canonical, active, PMF.pure_bind]

def stateLaw {split : Bool} (profile : Profile (model split).behavioralSignature)
    (state : State) : PMF State :=
  (fun law => law.bind (kernel profile))^[2] (PMF.pure state)

theorem branch_law (profile : Profile (model true).behavioralSignature) :
    stateLaw profile [some false] =
      (profile () [some false]).map (fun choice => [choice.val.getD none, some false]) := by
  simp [stateLaw, Function.iterate_succ_apply', kernel, active, PMF.pure_bind,
    ← PMF.bind_pure_comp, Function.comp_def]

theorem canonical_state_root (split goal : Bool) :
    stateLaw (canonical split goal) [] = PMF.pure [none] := by
  have law := canonical_root_law split goal
  rw [InformationModel.runBehavioral, run_states] at law
  exact law

theorem canonical_state_branch (goal : Bool) :
    stateLaw (canonical true goal) [some false] = PMF.pure [some goal, some false] := by
  rw [branch_law]
  simp [canonical, active, PMF.pure_map]

theorem reward_pair_le_one (goal : Bool) (action : Outcome) :
    reward goal [action, some false] ≤ 1 := by
  cases action with
  | none => norm_num [reward]
  | some bit => cases goal <;> cases bit <;> norm_num [reward]

theorem context_value {split : Bool} (assessment : (model split).BehavioralAssessment)
    (site : (model split).InformationSite ()) (goal : Bool)
    (alternative : (model split).BehavioralPolicy ()) :
    (assessment.continuationContext site (fun h => reward goal h.state) 2).value alternative =
      expect (stateLaw (Profile.update assessment.strategy () alternative) site.1)
        (reward goal) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  calc
    _ = expect (assessment.belief () site) (fun _ =>
        expect (stateLaw (Profile.update assessment.strategy () alternative) site.1)
          (reward goal)) := by
      apply expect_congr_on_support
      intro history _
      have same : history.1.state = site.1 := by simpa using history.2
      have laws := congrArg (fun law => expect law (reward goal))
        (run_states (Profile.update assessment.strategy () alternative) 2 history.1)
      simpa only [expect_map, Function.comp_def, same, stateLaw] using laws
    _ = _ := expect_constant _ _

theorem update_own (split : Bool) (profile : Profile (model split).behavioralSignature) :
    Profile.update profile () (profile ()) = profile := by
  funext who
  cases who
  exact Profile.update_same _ _ _

theorem canonical_rational (split goal : Bool)
    (assessment : (model split).BehavioralAssessment)
    (strategy : assessment.strategy = canonical split goal) :
    assessment.IsSequentiallyRationalWithin (fun _ h => reward goal h.state) 2 := by
  intro who site
  cases who
  refine ⟨payoffIntegrable_of_finite _ _, fun _ _ => payoffIntegrable_of_finite _ _,
    fun alternative _ => ?_⟩
  rw [context_value, context_value, update_own, strategy]
  obtain ⟨history, _, _⟩ := site.2
  have acts := InformationModel.InformationSite.active (model split) site history
  have same : history.1.state = site.1 := by simpa using history.2
  rw [same] at acts
  rcases acts with root | ⟨rfl, branch⟩
  · rw [root, canonical_state_root, expect_pure]
    change _ ≤ 2
    exact expect_le_const _ _ (reward_integrable _ _) _ (fun state _ => reward_le_two goal state)
  · rw [branch, canonical_state_branch, expect_pure]
    have value : reward goal [some goal, some false] = 1 := by simp [reward]
    rw [value, branch_law, expect_map]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
    intro choice _
    exact reward_pair_le_one goal _

def isEquilibrium (split goal : Bool) (assessment : (model split).BehavioralAssessment) : Prop :=
  assessment.IsSequentialEquilibriumFor (antichain split) (fun _ site =>
    assessment.continuationContext site (fun h => reward goal h.state) 2)

theorem exists_canonical_equilibrium (split goal : Bool) :
    ∃ assessment : (model split).BehavioralAssessment,
      assessment.strategy = canonical split goal ∧ isEquilibrium split goal assessment := by
  obtain ⟨assessment, strategy, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion
      (reference split) (reference_mixed split) (antichain split) (canonical split goal)
  exact ⟨assessment, strategy, canonical_rational split goal assessment strategy, consistent⟩

theorem exists_common_source_equilibrium :
    ∃ assessment : (model false).BehavioralAssessment,
      assessment.strategy = canonical false false ∧
      ∀ goal, isEquilibrium false goal assessment := by
  obtain ⟨assessment, strategy, equilibrium⟩ := exists_canonical_equilibrium false false
  refine ⟨assessment, strategy, fun goal => ⟨?_, equilibrium.2⟩⟩
  exact canonical_rational false goal assessment (strategy.trans (canonical_source goal).symm)

def branchHistory : (arena true).History :=
  (arena true).initHistory.extend (joint := fun _ => some (some false))
    (target := [some false])
    (by
      refine ⟨?_, fun _ => ?_⟩
      · simp [arena, active]
      · exact ⟨Or.inl rfl, by simp [available]⟩)
    ((PMF.mem_support_pure_iff _ _).mpr rfl)

def branchSite : (model true).InformationSite () :=
  (model true).informationSite () branchHistory (some false)
    (by simp [arena, active, branchHistory, History.extend, initHistory])
    (by exact ⟨Or.inr ⟨rfl, rfl⟩, rfl⟩)

@[simp] theorem branch_site_value : branchSite.1 = [some false] := rfl

theorem update_unit {split : Bool}
    (profile replacement : Profile (model split).behavioralSignature) :
    Profile.update profile () (replacement ()) = replacement := by
  funext who
  cases who
  exact Profile.update_same _ _ _

theorem rational_branch_value (goal : Bool) (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin (fun _ h => reward goal h.state) 2) :
    1 ≤ expect (stateLaw assessment.strategy [some false]) (reward goal) := by
  have bound := (rational () branchSite).2.2 ((canonical true goal) ()) (Set.mem_univ _)
  rw [context_value, context_value, update_own, update_unit, branch_site_value] at bound
  change expect (stateLaw (canonical true goal) [some false]) (reward goal) ≤ _ at bound
  rw [canonical_state_branch, expect_pure] at bound
  simpa only [reward, List.cons.injEq, List.cons_ne_self, and_false, ↓reduceIte,
    List.headD_cons, ite_eq_left rfl] using bound

theorem branch_opposite_reward_bound (profile : Profile (model true).behavioralSignature) :
    expect (stateLaw profile [some false]) (reward false) +
      expect (stateLaw profile [some false]) (reward true) ≤ 1 := by
  rw [← expect_add (reward_integrable _ _) (reward_integrable _ _), branch_law, expect_map]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
  intro choice _
  simp only [Function.comp_apply]
  cases action : choice.val.getD none with
  | none => norm_num [reward]
  | some bit => cases bit <;> norm_num [reward]

/-- The differing utilities cannot be reconciled by changing off-path beliefs:
the player must choose opposite actions at the same later decision. -/
theorem no_common_rational_strategy :
    ¬ ∃ first second : (model true).BehavioralAssessment,
      first.strategy = second.strategy ∧
      first.IsSequentiallyRationalWithin (fun _ h => reward false h.state) 2 ∧
      second.IsSequentiallyRationalWithin (fun _ h => reward true h.state) 2 := by
  rintro ⟨first, second, same, firstRational, secondRational⟩
  have firstValue := rational_branch_value false first firstRational
  have secondValue := rational_branch_value true second secondRational
  rw [← same] at secondValue
  have sum := branch_opposite_reward_bound first.strategy
  linarith

def outcomeLaw {split : Bool} (assessment : (model split).BehavioralAssessment) : PMF Outcome :=
  ((model split).runBehavioral assessment.strategy 2).map (fun h => h.state.headD none)

theorem canonical_outcome (split goal : Bool) (assessment : (model split).BehavioralAssessment)
    (strategy : assessment.strategy = canonical split goal) :
    outcomeLaw assessment = PMF.pure none := by
  have law := congrArg (fun law => law.map (fun state : State => state.headD none))
    (canonical_root_law split goal)
  simpa only [outcomeLaw, strategy, PMF.map_comp, PMF.pure_map, List.headD_cons,
    Function.comp_def] using law

/-- One source equilibrium works for both utilities. Its outcome is implementable
as a native SE separately for each utility, but no utility-independent profile
translator preserves it for both. The translator may inspect the whole profile;
this already rules out the more restrictive playerwise compiler. -/
theorem outcome_implementation_without_uniform_compiler :
    ∃ source : (model false).BehavioralAssessment,
      (∀ goal, isEquilibrium false goal source) ∧
      (∀ goal, ∃ target : (model true).BehavioralAssessment,
        isEquilibrium true goal target ∧ outcomeLaw target = outcomeLaw source) ∧
      ¬ ∃ translate : Profile (model false).behavioralSignature →
          Profile (model true).behavioralSignature,
        ∀ goal, ∃ target : (model true).BehavioralAssessment,
          target.strategy = translate source.strategy ∧ isEquilibrium true goal target := by
  obtain ⟨source, sourceStrategy, sourceEquilibrium⟩ := exists_common_source_equilibrium
  refine ⟨source, sourceEquilibrium, ?_, ?_⟩
  · intro goal
    obtain ⟨target, strategy, equilibrium⟩ := exists_canonical_equilibrium true goal
    exact ⟨target, equilibrium, (canonical_outcome true goal target strategy).trans
      (canonical_outcome false false source sourceStrategy).symm⟩
  · rintro ⟨translate, translates⟩
    obtain ⟨first, firstStrategy, firstEquilibrium⟩ := translates false
    obtain ⟨second, secondStrategy, secondEquilibrium⟩ := translates true
    exact no_common_rational_strategy ⟨first, second,
      firstStrategy.trans secondStrategy.symm, firstEquilibrium.1, secondEquilibrium.1⟩

end GameTheoryExtensionsTests.CoalescingEquilibrium
