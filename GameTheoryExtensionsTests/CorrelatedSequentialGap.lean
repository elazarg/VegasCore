/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion
import GameTheory.Protocol.StateKernel
import GameTheory.Core.Equilibrium
import GameTheory.Core.Utility
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Normal-form correlation does not record credible continuations

The entrant (`false`) chooses Out/Enter; the incumbent (`true`) chooses
Fight/Accommodate. In the simultaneous presentation both choose initially.
In the sequential presentation the incumbent chooses only after Enter.
The public result is Out, Fight, or Accommodate, and the pure normal-form
outcome map is the same in both presentations.

Out pays `(1, 2)`, Fight pays `(-1, -1)`, and Accommodate pays `(2, 1)`.
Out/Fight is a simultaneous sequential equilibrium and a correlated equilibrium
of either normal form. In the sequential presentation, accommodation is strictly
optimal after entry, so sequential rationality makes entering worth two. No
target sequential equilibrium has the source equilibrium's Out outcome. Thus
even preserving every normal-form CE for every preference does not preserve
sequential-equilibrium outcome laws for one fixed, non-zero-sum utility.
-/

noncomputable section

namespace GameTheoryExtensionsTests.CorrelatedSequentialGap

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

abbrev State := List (Bool × Bool)
abbrev Outcome := Option Bool

@[reducible] def running (sequential : Bool) (state : State) : Prop :=
  state = [] ∨ sequential = true ∧ state = [(true, false)]

@[reducible] def active (sequential : Bool) (state : State) (who : Bool) : Prop :=
  state = [] ∧ (sequential = false ∨ who = false) ∨
    sequential = true ∧ state = [(true, false)] ∧ who = true

def next (state : State) (joint : Bool → Option Bool) : State :=
  (if state = [] then ((joint false).getD false, (joint true).getD false)
    else (true, (joint true).getD false)) :: state

@[reducible] def arena (sequential : Bool) : ExecutionProtocol Bool where
  State := State
  Action _ := Bool
  init := []
  active state who := active sequential state who
  available _ _ := Set.univ
  terminal state := ¬ running sequential state
  step state joint := PMF.pure (next state joint.1)
  progress state _ := by
    classical
    refine ⟨fun who => if active sequential state who then some false else none, ?_⟩
    intro who
    by_cases acts : active sequential state who <;> simp [acts]

@[reducible] def signals (sequential : Bool) : InfoSignals (arena sequential) where
  PublicSignal := Unit
  PrivateSignal _ := State
  initialPublic := ()
  initialPrivate _ := []
  publicSignal _ := ()
  privateSignal _ event := event.target
  InfoState _ := State
  initInfo _ secret _ := secret
  pushInfo _ _ _ secret _ := secret

@[simp] theorem info_state (sequential who : Bool) : ∀ {state : State}
    (trace : (arena sequential).Trace state), (signals sequential).infoOf who trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def model (sequential : Bool) : InformationModel (arena sequential) where
  toInfoSignals := signals sequential
  menu who state := {choice | match choice with
    | some _ => active sequential state who
    | none => ¬ active sequential state who}
  menu_adequate := by
    intro who state trace choice
    rw [info_state]
    cases choice <;> simp [LegalOption]

theorem history_length (sequential : Bool) : ∀ {state : State}
    (trace : (arena sequential).Trace state), trace.length = state.length
  | _, .start => rfl
  | _, .extend prior _ _ realized => by
      cases (PMF.mem_support_pure_iff _ _).mp realized
      simpa only [Trace.length, next, List.length_cons] using
        congrArg (· + 1) (history_length sequential prior)

theorem bounded (sequential : Bool) : (arena sequential).BoundedHorizon 2 := by
  intro state trace enough
  rw [history_length] at enough
  change ¬ running sequential state
  rintro (rfl | ⟨_, rfl⟩) <;> simp_all

def choose (sequential : Bool) (action who : Bool) (state : State) :
    (model sequential).Choice who state :=
  if acts : active sequential state who then ⟨some action, acts⟩ else ⟨none, acts⟩

def canonical (sequential : Bool) (actions : Bool → Bool) :
    Profile (model sequential).behavioralSignature := fun who state =>
  PMF.pure (choose sequential (actions who) who state)

instance (sequential who : Bool) (state : State) :
    Fintype ((model sequential).Choice who state) := by
  classical
  exact Fintype.ofFinite _

instance (sequential who : Bool) (state : State) :
    Nonempty ((model sequential).Choice who state) :=
  ⟨((canonical sequential fun _ => false) who state).support_nonempty.choose⟩

def reference (sequential : Bool) : (model sequential).BehavioralAssessment :=
  .ofStrategy (fun _ _ => (PMF.uniformOfFintype _))

theorem reference_mixed (sequential : Bool) : (reference sequential).IsFullyMixed := by
  intro who site choice
  exact PMF.mem_support_uniformOfFintype choice

instance (sequential : Bool) : Finite (arena sequential).History :=
  (reference_mixed sequential).finite_history (bounded sequential) (fun _ _ => Set.toFinite _)
    (fun _ => by simp)

instance (sequential : Bool) : Fintype (arena sequential).History := Fintype.ofFinite _

instance (sequential who : Bool) (site : (model sequential).InformationSite who) :
    Fintype ((model sequential).InformationHistory who site.1) := by
  classical
  infer_instance

theorem antichain (sequential : Bool) : (model sequential).DecisionInformationAntichain := by
  intro who site first second joint legal target realized fuel reached
  have firstState : first.1.state = site.1 := by simpa using first.2
  have secondState : second.1.state = site.1 := by simpa using second.2
  have increases := reached.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at increases
  rw [history_length, history_length, firstState, secondState] at increases
  omega

def kernel {sequential : Bool} (profile : Profile (model sequential).behavioralSignature)
    (state : State) : PMF State :=
  if running sequential state then
    (independentProduct (fun who => profile who state)).map
      (fun joint => next state (fun who => (joint who).val))
  else PMF.pure state

theorem chooser_kernel {sequential : Bool}
    (profile : Profile (model sequential).behavioralSignature)
    (history : (arena sequential).History) (live : ¬ (arena sequential).terminal history.state) :
    ((model sequential).randomizedChooser profile history live).bind
      ((arena sequential).step history.state) = kernel profile history.state := by
  have runs : running sequential history.state := not_not.mp live
  rcases history with ⟨state, trace⟩
  cases trace <;>
    simp [InformationModel.randomizedChooser, InformationModel.behavioralJoint,
      arena, kernel, runs, ← PMF.bind_pure_comp, Function.comp_def, InfoSignals.infoOf, signals]

theorem run_states {sequential : Bool}
    (profile : Profile (model sequential).behavioralSignature) (fuel : Nat)
    (history : (arena sequential).History) :
    ((model sequential).runBehavioralFrom profile fuel history).map History.state =
      (fun law => law.bind (kernel profile))^[fuel] (PMF.pure history.state) := by
  apply runRandomizedFor_map_state
  · intro state stopped
    exact ite_eq_right stopped
  · exact chooser_kernel profile

def stateLaw {sequential : Bool} (profile : Profile (model sequential).behavioralSignature)
    (state : State) : PMF State :=
  (fun law => law.bind (kernel profile))^[2] (PMF.pure state)

def outcome (state : State) : Outcome :=
  if (state.headD (false, false)).1 then some (state.headD (false, false)).2 else none

def utility (who : Bool) : Outcome → ℝ
  | none => if who then 2 else 1
  | some false => -1
  | some true => if who then 1 else 2

def reward (who : Bool) (state : State) : ℝ := utility who (outcome state)

theorem context_value {sequential : Bool}
    (assessment : (model sequential).BehavioralAssessment) (who : Bool)
    (site : (model sequential).InformationSite who)
    (alternative : (model sequential).BehavioralPolicy who) :
    (assessment.truncatedContinuationContext site (reward who ·.state) 2).value alternative =
      expect (stateLaw (Profile.update assessment.strategy who alternative) site.1)
        (reward who) := by
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  calc
    _ = expect (assessment.belief who site) (fun _ =>
        expect (stateLaw (Profile.update assessment.strategy who alternative) site.1)
          (reward who)) := by
      apply expect_congr_on_support
      intro history _
      have same : history.1.state = site.1 := by simpa using history.2
      have laws := congrArg (fun law => expect law (reward who))
        (run_states (Profile.update assessment.strategy who alternative) 2 history.1)
      simpa only [expect_map, Function.comp_def, same, stateLaw] using laws
    _ = _ := expect_constant _ _

theorem canonical_root_outcome (sequential : Bool) (actions : Bool → Bool) :
    (stateLaw (canonical sequential actions) []).map outcome =
      PMF.pure (if actions false then some (actions true) else none) := by
  cases entrant : actions false <;> cases incumbent : actions true <;> cases sequential <;>
    simp [stateLaw, Function.iterate_succ_apply', kernel, canonical, choose,
      running, active, next, entrant, incumbent, outcome, independentProduct_pure, PMF.pure_map]

theorem source_root_law (profile : Profile (model false).behavioralSignature) :
    stateLaw profile [] =
      (independentProduct (fun who => profile who [])).map
        (fun joint => [((joint false).val.getD false, (joint true).val.getD false)]) := by
  simp [stateLaw, Function.iterate_succ_apply', kernel, running, next,
    ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind]

def prescribed (sequential : Bool) : Profile (model sequential).behavioralSignature :=
  canonical sequential (fun _ => false)

theorem prescribed_root_value (sequential who : Bool) :
    expect (stateLaw (prescribed sequential) []) (reward who) = if who then 2 else 1 := by
  have law := congrArg (fun law => expect law (utility who))
    (canonical_root_outcome sequential (fun _ => false))
  change expect (stateLaw (canonical sequential fun _ => false) [])
    (fun state => utility who (outcome state)) = _
  simpa only [expect_map, Function.comp_def, Bool.false_eq_true, ↓reduceIte, expect_pure,
    utility] using law

theorem source_deviation_bound (who : Bool) (alternative : (model false).BehavioralPolicy who) :
    expect (stateLaw (Profile.update (prescribed false) who alternative) []) (reward who) ≤
      if who then 2 else 1 := by
  rw [source_root_law, expect_map]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
  intro joint supported
  simp only [Function.comp_apply]
  have opponent := ((independentProduct_support_iff _ _).mp supported) (!who)
  have opponentChoice : joint (!who) = choose false false (!who) [] := by
    cases who <;> simpa [Profile.update, prescribed, canonical] using opponent
  cases who
  · change joint true = choose false false true [] at opponentChoice
    have value : (joint true).val = some false := by
      rw [opponentChoice]
      simp [choose, active]
    simp only [reward, outcome, List.headD_cons, value, Option.getD_some, utility]
    cases (joint false).val.getD false <;> norm_num
  · change joint false = choose false false false [] at opponentChoice
    have value : (joint false).val = some false := by
      rw [opponentChoice]
      simp [choose, active]
    simp [reward, outcome, value, utility]

theorem source_rational (assessment : (model false).BehavioralAssessment)
    (strategy : assessment.strategy = prescribed false) :
    assessment.IsSequentiallyRationalFor fun who site =>
        assessment.truncatedContinuationContext site (fun h => reward who h.state) 2 := by
  intro who site
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    fun _ _ => payoffIntegrable_of_finite _ _).mpr fun alternative _ => ?_
  obtain ⟨history, _, _⟩ := site.2
  have acts := InformationModel.InformationSite.active (model false) site history
  have same : history.1.state = site.1 := by simpa using history.2
  have atRoot : site.1 = [] := by
    rw [same] at acts
    simpa [arena, active] using acts
  rw [context_value, context_value, Profile.update_eq_self, strategy, atRoot,
    prescribed_root_value]
  exact source_deviation_bound who alternative

def isEquilibrium (sequential : Bool) (assessment : (model sequential).BehavioralAssessment) :
    Prop := assessment.IsSequentialEquilibriumFor (antichain sequential) (fun who site =>
      assessment.truncatedContinuationContext site (fun h => reward who h.state) 2)

theorem exists_source_equilibrium :
    ∃ assessment : (model false).BehavioralAssessment,
      assessment.strategy = prescribed false ∧ isEquilibrium false assessment := by
  obtain ⟨assessment, strategy, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion
      (reference false) (reference_mixed false) (antichain false) (prescribed false)
  exact ⟨assessment, strategy, source_rational assessment strategy, consistent⟩

def actionLaw {sequential : Bool} (profile : Profile (model sequential).behavioralSignature)
    (who : Bool) (state : State) : PMF Bool :=
  (profile who state).map (fun choice => choice.val.getD false)

theorem branch_kernel (profile : Profile (model true).behavioralSignature) :
    kernel profile [(true, false)] =
      (actionLaw profile true [(true, false)]).map
        (fun action => [(true, action), (true, false)]) := by
  have marginal := independentProduct_map_eval (fun who => profile who [(true, false)]) true
  have mapped := congrArg (fun law => law.map
    (fun choice : (model true).Choice true [(true, false)] =>
      [(true, choice.val.getD false), (true, false)])) marginal
  simpa only [kernel, running, or_true, and_self, ite_true, next,
    List.cons_ne_nil, ↓reduceIte, PMF.map_comp, Function.comp_def, actionLaw] using mapped

theorem root_kernel (profile : Profile (model true).behavioralSignature) :
    kernel profile [] = (actionLaw profile false []).map
      (fun action => [(action, false)]) := by
  have idle (choice : (model true).Choice true []) : choice.val = none := by
    have permitted := choice.property
    cases value : choice.val <;> simp_all [model, active]
  have marginal := independentProduct_map_eval (fun who => profile who []) false
  have mapped := congrArg (fun law => law.map
    (fun choice : (model true).Choice false [] => [(choice.val.getD false, false)])) marginal
  simpa only [kernel, running, true_or, ite_true, next, ↓reduceIte,
    idle, Option.getD_none, PMF.map_comp, Function.comp_def, actionLaw] using mapped

theorem branch_law (profile : Profile (model true).behavioralSignature) :
    stateLaw profile [(true, false)] =
      (actionLaw profile true [(true, false)]).map
        (fun action => [(true, action), (true, false)]) := by
  simp only [stateLaw, Function.iterate_succ_apply', Function.iterate_zero_apply,
    PMF.pure_bind, branch_kernel, PMF.bind_map]
  simp [kernel, running, ← PMF.bind_pure_comp, Function.comp_def]

theorem target_root_law (profile : Profile (model true).behavioralSignature) :
    stateLaw profile [] = (actionLaw profile false []).bind (fun action =>
      if action then stateLaw profile [(true, false)] else PMF.pure [(false, false)]) := by
  simp only [stateLaw, Function.iterate_succ_apply', Function.iterate_zero_apply,
    PMF.pure_bind, root_kernel, PMF.bind_map]
  apply bind_congr_on_support _
  intro action _
  cases action
  · simp [kernel, running]
  · simp only [Function.comp_apply, ↓reduceIte]
    rw [branch_kernel, PMF.bind_map, ← PMF.bind_pure_comp]
    apply bind_congr_on_support
    intro action _
    simp [kernel, running]

def branchHistory : (arena true).History :=
  (arena true).initHistory.extend (joint := fun who => if who then none else some true)
    (target := [(true, false)])
    (by
      refine ⟨?_, fun who => ?_⟩
      · simp [arena, running]
      · cases who <;> simp [arena, active])
    ((PMF.mem_support_pure_iff _ _).mpr rfl)

def branchSite : (model true).InformationSite true :=
  (model true).informationSite true branchHistory true
    (by simp [arena, running, branchHistory, History.extend, initHistory])
    (by exact Or.inr ⟨rfl, rfl, rfl⟩)

def rootSite : (model true).InformationSite false :=
  (model true).informationSite false (arena true).initHistory true
    (by simp [arena, running, initHistory])
    (by exact Or.inl ⟨rfl, Or.inr rfl⟩)

theorem branch_deviation_value (profile : Profile (model true).behavioralSignature) :
    expect (stateLaw (Profile.update profile true ((canonical true (fun _ => true)) true))
      [(true, false)]) (reward true) = 1 := by
  rw [branch_law]
  simp [actionLaw, canonical, choose, active, reward, outcome, utility, PMF.pure_map,
    expect_pure]

theorem rational_branch_value (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalFor fun who site =>
        assessment.truncatedContinuationContext site (fun h => reward who h.state) 2) :
    1 ≤ expect (stateLaw assessment.strategy [(true, false)]) (reward true) := by
  have improves := (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    fun _ _ => payoffIntegrable_of_finite _ _).mp (rational true branchSite)
      ((canonical true fun _ => true) true)
    (Set.mem_univ _)
  rw [context_value, context_value, Profile.update_eq_self] at improves
  change expect (stateLaw _ [(true, false)]) _ ≤ _ at improves
  rw [branch_deviation_value] at improves
  exact improves

theorem branch_payoff_relation (profile : Profile (model true).behavioralSignature) :
    expect (stateLaw profile [(true, false)]) (reward false) =
      (3 / 2 : ℝ) * expect (stateLaw profile [(true, false)]) (reward true) + 1 / 2 := by
  rw [branch_law, expect_map, expect_map]
  calc
    _ = expect (actionLaw profile true [(true, false)])
        (fun action => (3 / 2 : ℝ) * reward true [(true, action), (true, false)] + 1 / 2) := by
      apply expect_congr_on_support
      intro action _
      cases action <;> norm_num [reward, outcome, utility]
    _ = _ := by rw [expect_add_of_finite, expect_constant, expect_const_mul]; rfl

theorem enter_deviation_value (profile : Profile (model true).behavioralSignature) :
    expect (stateLaw (Profile.update profile false ((canonical true (fun _ => true)) false)) [])
      (reward false) = expect (stateLaw profile [(true, false)]) (reward false) := by
  rw [target_root_law]
  simp only [actionLaw, Profile.update_same, canonical, choose,
    show active true [] false from Or.inl ⟨rfl, Or.inr rfl⟩, dite_true,
    PMF.pure_map, Option.getD_some, PMF.pure_bind, ite_true]
  rw [branch_law, branch_law]
  simp [actionLaw, Profile.update]

theorem rational_root_value (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalFor fun who site =>
        assessment.truncatedContinuationContext site (fun h => reward who h.state) 2) :
    2 ≤ expect (stateLaw assessment.strategy []) (reward false) := by
  have incumbent := rational_branch_value assessment rational
  have relation := branch_payoff_relation assessment.strategy
  have improves := (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    fun _ _ => payoffIntegrable_of_finite _ _).mp (rational false rootSite)
      ((canonical true fun _ => true) false)
    (Set.mem_univ _)
  rw [context_value, context_value, Profile.update_eq_self] at improves
  change expect (stateLaw _ []) _ ≤ _ at improves
  rw [enter_deviation_value] at improves
  change expect (stateLaw assessment.strategy [(true, false)]) (reward false) ≤
    expect (stateLaw assessment.strategy []) (reward false) at improves
  linarith

def outcomeLaw {sequential : Bool} (assessment : (model sequential).BehavioralAssessment) :
    PMF Outcome :=
  ((model sequential).runBehavioral assessment.strategy 2).map
    (fun history => outcome history.state)

theorem outcomeLaw_state {sequential : Bool}
    (assessment : (model sequential).BehavioralAssessment) :
    outcomeLaw assessment = (stateLaw assessment.strategy []).map outcome := by
  have law := congrArg (fun law => law.map outcome)
    (run_states assessment.strategy 2 (arena sequential).initHistory)
  simpa only [outcomeLaw, InformationModel.runBehavioral, PMF.map_comp,
    Function.comp_def, stateLaw, initHistory] using law

/-- Even changing the entire target strategy and all off-path beliefs cannot
recover the Out outcome as a sequential equilibrium. -/
theorem no_target_equilibrium_out (assessment : (model true).BehavioralAssessment)
    (equilibrium : isEquilibrium true assessment) : outcomeLaw assessment ≠ PMF.pure none := by
  intro same
  have value := rational_root_value assessment equilibrium.1
  have observed := congrArg (fun law => expect law (utility false)) same
  rw [outcomeLaw_state, expect_map, expect_pure] at observed
  change expect (stateLaw assessment.strategy []) (reward false) = 1 at observed
  linarith

@[reducible] def signature : GameSignature Bool where
  Strategy _ := Bool
  Outcome := Outcome

/-- The ordinary pure normal form, obtained by running each presentation's
actual protocol. Each player has one decision and chooses one Boolean action. -/
def normalForm (sequential : Bool) : GameForm Bool where
  sig := signature
  play actions := ((model sequential).runBehavioral (canonical sequential actions) 2).map
    (fun history => outcome history.state)

theorem normalForm_play (sequential : Bool) (actions : Profile signature) :
    (normalForm sequential).play actions =
      PMF.pure (if actions false then some (actions true) else none) := by
  have law := outcomeLaw_state
    (InformationModel.BehavioralAssessment.ofStrategy (canonical sequential actions))
  change (normalForm sequential).play actions =
    (stateLaw (canonical sequential actions) []).map outcome at law
  exact law.trans (canonical_root_outcome sequential actions)

/-- Normal-form outcome laws agree for every profile, independently of utilities. -/
theorem normalForm_equal : normalForm true = normalForm false := by
  have same : (normalForm true).play = (normalForm false).play := by
    funext actions
    rw [normalForm_play, normalForm_play]
  exact congrArg (fun play => ({sig := signature, play := play} : GameForm Bool)) same

/-- Hence the complete CE correspondence agrees, for every preference, not only
for the utility witnessing the credibility failure below. -/
theorem correlated_equilibrium_iff (preference : WeakPreference Bool Outcome)
    (law : PMF (Profile signature)) :
    IsCorrelatedEq (normalForm true) preference law ↔
      IsCorrelatedEq (normalForm false) preference law := by
  simp only [isCorrelatedEq_iff, GameForm.outcomeLaw, normalForm_play]
  have same : (normalForm true).play = (normalForm false).play := by
    funext actions
    rw [normalForm_play, normalForm_play]
  rw [same]
  rfl

theorem threat_nash (sequential : Bool) :
    IsNash (normalForm sequential) (euPreference (fun result who => utility who result))
      (fun _ => false) := by
  rw [isNash_iff]
  intro who replacement
  rw [normalForm_play, normalForm_play,
    euPreference_iff _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
    expectedUtility_pure, expectedUtility_pure]
  cases who <;> cases replacement <;> norm_num [Profile.update, utility]

theorem threat_correlated (sequential : Bool) :
    IsCorrelatedEq (normalForm sequential) (euPreference (fun result who => utility who result))
      (PMF.pure (fun _ => false)) := (threat_nash sequential).isCorrelatedEq

/-- Preserving all normal-form CE laws, even for every utility, does not imply
preserving sequential-equilibrium outcome laws for this fixed utility. -/
theorem correlated_preservation_without_sequential_outcome_preservation :
    (∀ preference law, IsCorrelatedEq (normalForm true) preference law ↔
      IsCorrelatedEq (normalForm false) preference law) ∧
    ∃ source : (model false).BehavioralAssessment,
      isEquilibrium false source ∧
      ¬ ∃ target : (model true).BehavioralAssessment,
        isEquilibrium true target ∧ outcomeLaw target = outcomeLaw source := by
  refine ⟨correlated_equilibrium_iff, ?_⟩
  obtain ⟨source, strategy, equilibrium⟩ := exists_source_equilibrium
  refine ⟨source, equilibrium, ?_⟩
  have sourceLaw : outcomeLaw source = PMF.pure none := by
    rw [outcomeLaw_state, strategy]
    exact canonical_root_outcome false (fun _ => false)
  rintro ⟨target, targetEquilibrium, same⟩
  exact no_target_equilibrium_out target targetEquilibrium (same.trans sourceLaw)

end GameTheoryExtensionsTests.CorrelatedSequentialGap
