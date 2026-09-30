/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationAbstraction
import GameTheoryExtensions.Analysis.Protocol.LastDecision
import GameTheory.Protocol.StateKernel
import GameTheory.Protocol.SingleMover
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Terminal decision experiments as protocol games

Nature samples a latent state from a fixed prior, the sole player observes a
signal and chooses one public action, and execution terminates. Only states in
the prior's support give legal decision histories; player strategies never
determine which histories are legal.

For finite latent states and finite nonempty action menus, Bayesian optimality
is equivalent to the existing protocol sequential-equilibrium predicate with
the unique consistent beliefs. One common fully mixed sequence establishes
consistency. The initialized result law is the decision experiment's fact/action
law, and the final theorem characterizes all-utility outcome preservation under
deterministic observation erasure relative to a fully informed concrete player.
-/

noncomputable section

namespace GameTheory.DecisionExperiment

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Math.Probability

variable {State Signal Action : Type}

inductive Node (State Action : Type) where
  | initial
  | decision (state : State)
  | done (state : State) (action : Action)
  deriving DecidableEq

namespace Protocol

variable (prior : PMF State) (observe : State → Signal) [Nonempty Action]

def terminal : Node State Action → Prop
  | .done _ _ => True
  | _ => False

def active : Node State Action → Prop
  | .decision _ => True
  | _ => False

def transition (node : Node State Action) (joint : Unit → Option Action) :
    PMF (Node State Action) :=
  match node with
  | .initial => prior.map Node.decision
  | .decision state => PMF.pure (.done state ((joint ()).getD (Classical.choice inferInstance)))
  | .done state action => PMF.pure (.done state action)

@[reducible] def arena : ExecutionProtocol Unit where
  State := Node State Action
  Action _ := Action
  init := .initial
  active node _ := active node
  available _ _ := Set.univ
  terminal := terminal
  step node joint := transition prior node joint.1
  progress node running := by
    classical
    refine ⟨fun _ => if active node then some (Classical.choice inferInstance) else none, ?_⟩
    intro who
    by_cases enabled : active node <;> simp [enabled]

def depth : Node State Action → Nat
  | .initial => 0
  | .decision _ => 1
  | .done _ _ => 2

theorem history_length : ∀ {node} (trace : (arena (Action := Action) prior).Trace node),
    trace.length = depth node
  | _, .start => rfl
  | _, .extend (source := before) earlier joint legal realized => by
      have previous := history_length earlier
      cases before with
      | initial =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ realized
          simpa only [Trace.length, depth] using congrArg (· + 1) previous
      | decision state =>
          cases (PMF.mem_support_pure_iff _ _).mp realized
          simpa only [Trace.length, depth] using congrArg (· + 1) previous
      | done state action => exact (legal.1 trivial).elim

theorem bounded : (arena (Action := Action) prior).BoundedHorizon 2 := by
  intro node trace enough
  rw [history_length prior trace] at enough
  cases node <;> simp_all [depth, terminal]

/-- Terminal play of the decision arena, certified by its horizon. -/
theorem certificate : (arena (Action := Action) prior).WellFoundedHistories :=
  (bounded prior).wellFoundedHistories

theorem single : ∀ node {first second},
    (arena (Action := Action) prior).active node first →
      (arena (Action := Action) prior).active node second → first = second :=
  fun _ _ _ _ _ => Subsingleton.elim _ _

def observation : Node State Action → Option Signal
  | .decision state => some (observe state)
  | _ => none

@[reducible] def signals : InfoSignals (arena (Action := Action) prior) where
  PublicSignal := Unit
  PrivateSignal _ := Option Signal
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal _ event := observation observe event.target
  InfoState _ := Option Signal
  initInfo _ secret _ := secret
  pushInfo _ _ _ secret _ := secret

theorem info_state (who : Unit) : ∀ {node} (trace : (arena (Action := Action) prior).Trace node),
    (signals (Action := Action) prior observe).infoOf who trace = observation observe node
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def model : InformationModel (arena (Action := Action) prior) where
  toInfoSignals := signals (Action := Action) prior observe
  menu _ info := {choice | choice.isSome = info.isSome}
  menu_adequate who node trace choice := by
    rw [info_state]
    cases node <;> cases choice <;> simp [observation, LegalOption, arena, active]

theorem initial_legal :
    (arena (Action := Action) prior).Legal .initial (fun _ => none) :=
  ⟨id, fun _ => by simp [active]⟩

theorem decision_legal (state : State) (action : Action) :
    (arena (Action := Action) prior).Legal (.decision state) (fun _ => some action) :=
  ⟨id, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

def decisionHistory (state : State) (supported : state ∈ prior.support) :
    (arena (Action := Action) prior).History :=
  (arena (Action := Action) prior).initHistory.extend
    (target := .decision state) (initial_legal prior) (by
    change Node.decision state ∈ (prior.map (Node.decision (Action := Action))).support
    rw [PMF.support_map]
    exact ⟨state, supported, rfl⟩)

def terminalHistory (state : State) (supported : state ∈ prior.support) (action : Action) :
    (arena (Action := Action) prior).History :=
  (decisionHistory (Action := Action) prior state supported).extend
    (decision_legal prior state action)
    ((PMF.mem_support_pure_iff _ _).mpr rfl)

theorem initial_joint (joint : Unit → Option Action)
    (legal : (arena (Action := Action) prior).Legal .initial joint) : joint = fun _ => none := by
  funext who
  exact LegalOption.eq_none_of_inactive (E := arena (Action := Action) prior) (joint who)
    ((arena (Action := Action) prior).legalOption_of_legal legal who) (by simp [active])

theorem decision_joint (state : State) (joint : Unit → Option Action)
    (legal : (arena (Action := Action) prior).Legal (.decision state) joint) :
    ∃ action, joint = fun _ => some action := by
  obtain ⟨action, same⟩ := LegalOption.exists_eq_some_of_active
    (E := arena (Action := Action) prior) (joint ())
    ((arena (Action := Action) prior).legalOption_of_legal legal ()) trivial
  exact ⟨action, funext (fun who => by cases who; exact same)⟩

def Classified (history : (arena (Action := Action) prior).History) : Prop :=
  history = (arena (Action := Action) prior).initHistory ∨
    (∃ state supported, history = decisionHistory (Action := Action) prior state supported) ∨
      ∃ state supported action, history = terminalHistory prior state supported action

theorem classified_step (history : (arena (Action := Action) prior).History)
    (known : Classified prior history) (joint : Unit → Option Action)
    (legal : (arena (Action := Action) prior).Legal history.state joint) (node : Node State Action)
    (realized : node ∈
      ((arena (Action := Action) prior).step history.state ⟨joint, legal⟩).support) :
    Classified prior (history.extend legal realized) := by
  rcases known with rfl | ⟨state, supported, rfl⟩ | ⟨state, supported, action, rfl⟩
  · have same := initial_joint prior joint legal
    subst joint
    obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ realized
    exact Or.inr (Or.inl ⟨state, supported, rfl⟩)
  · obtain ⟨action, same⟩ := decision_joint prior state joint legal
    subst joint
    cases (PMF.mem_support_pure_iff _ _).mp realized
    exact Or.inr (Or.inr ⟨state, supported, action, rfl⟩)
  · exact (legal.1 trivial).elim

theorem classified : ∀ {node} (trace : (arena (Action := Action) prior).Trace node),
    Classified prior ⟨node, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend earlier joint legal realized =>
      classified_step prior _ (classified earlier) joint legal _ realized

theorem state_injective :
    Function.Injective (History.state (E := arena (Action := Action) prior)) := by
  intro first second same
  have left : Classified prior first := classified prior first.trace
  have right : Classified prior second := classified prior second.trace
  rcases left with rfl | ⟨state, supported, rfl⟩ | ⟨state, supported, action, rfl⟩
  all_goals rcases right with rfl | ⟨other, present, rfl⟩ | ⟨other, present, move, rfl⟩
  all_goals try cases same
  all_goals rfl

def choice (signal : Signal) (action : Action) :
    (model (Action := Action) prior observe).Choice () (some signal) :=
  ⟨some action, rfl⟩

def policy (response : Signal → PMF Action) :
    (model (Action := Action) prior observe).BehavioralPolicy ()
  | none => PMF.pure ⟨none, rfl⟩
  | some signal => (response signal).map (choice prior observe signal)

def response (strategy : (model (Action := Action) prior observe).BehavioralPolicy ())
    (signal : Signal) :
    PMF Action :=
  (strategy (some signal)).map fun selected =>
    selected.1.getD (Classical.choice inferInstance)

theorem response_policy (original : Signal → PMF Action) :
    response prior observe (policy prior observe original) = original := by
  funext signal
  simp only [response, policy, PMF.map_comp]
  exact PMF.map_id _

theorem choiceLaw_eq (strategy : (model (Action := Action) prior observe).BehavioralPolicy ())
    (signal : Signal) :
    (response prior observe strategy signal).map (choice prior observe signal) =
      strategy (some signal) := by
  rw [response, PMF.map_comp]
  conv_rhs => rw [← PMF.map_id (strategy (some signal))]
  apply map_congr_on_support _
  intro selected _
  apply Subtype.ext
  have legal := selected.2
  change selected.1.isSome = true at legal
  cases chosen : selected.1 with
  | none => simp [chosen] at legal
  | some action => simp [choice, chosen]

theorem policy_response (strategy : (model (Action := Action) prior observe).BehavioralPolicy ()) :
    policy prior observe (response prior observe strategy) = strategy := by
  funext info
  cases info with
  | none =>
      have all (selected : (model (Action := Action) prior observe).Choice () none) :
          selected = ⟨none, rfl⟩ := by
        apply Subtype.ext
        have legal := selected.2
        change selected.1.isSome = false at legal
        cases chosen : selected.1 with
        | none => rfl
        | some action => simp [chosen] at legal
      symm
      exact pmf_eq_pure_of_support_subset_singleton _ _ (fun selected _ => all selected)
  | some signal => exact choiceLaw_eq prior observe strategy signal

def kernel (profile : Profile (model (Action := Action) prior observe).behavioralSignature) :
    Node State Action → PMF (Node State Action)
  | .initial => prior.map Node.decision
  | .decision state => (response prior observe (profile ()) (observe state)).map (Node.done state)
  | .done state action => PMF.pure (.done state action)

theorem chooser_kernel
    (profile : Profile (model (Action := Action) prior observe).behavioralSignature)
    (history : (arena (Action := Action) prior).History)
    (running : ¬ (arena prior).terminal history.state) :
    ((model prior observe).singleMoverChooser (single prior) profile history running).bind
      ((arena prior).step history.state) = kernel prior observe profile history.state := by
  rcases history with ⟨node, trace⟩
  cases node with
  | initial => simp [arena, transition, kernel]
  | decision state =>
      have marginal := (model prior observe).singleMoverJoint_marginal (single prior)
        profile ⟨_, trace⟩ running ()
      rw [info_state] at marginal
      change ((model prior observe).singleMoverJoint (single prior) profile ⟨_, trace⟩ running).map
        (fun joint => joint.1 ()) = (profile () (some (observe state))).map Subtype.val at marginal
      have mapped := congrArg (fun law => law.map
        (fun selected : Option Action => Node.done state
          (selected.getD (Classical.choice inferInstance)))) marginal
      simpa only [InformationModel.singleMoverChooser, arena, transition,
        kernel, response, observation, PMF.map_comp, Function.comp_def,
        ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind] using mapped
  | done state action => exact (running trivial).elim

theorem run_states (profile : Profile (model (Action := Action) prior observe).behavioralSignature)
    (fuel : Nat) (history : (arena (Action := Action) prior).History) :
    ((model prior observe).runBehavioralFrom profile fuel history).map History.state =
      (fun law => law.bind (kernel prior observe profile))^[fuel]
        (PMF.pure history.state) := by
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom _ (single prior)]
  apply runRandomizedFor_map_state
  · intro node stopped
    cases node <;> try contradiction
    rfl
  · exact chooser_kernel prior observe profile

theorem run_decision
    (profile : Profile (model (Action := Action) prior observe).behavioralSignature)
    (state : State) (supported : state ∈ prior.support) :
    ((model prior observe).runBehavioralFrom profile 2
      (decisionHistory (Action := Action) prior state supported)).map History.state =
        (response prior observe (profile ()) (observe state)).map (Node.done state) := by
  rw [run_states]
  simp [Function.iterate_succ_apply', kernel, decisionHistory, History.extend,
    ← PMF.bind_pure_comp, Function.comp_def]

theorem run_initial
    (profile : Profile (model (Action := Action) prior observe).behavioralSignature) :
    ((model prior observe).runBehavioral profile 2).map History.state =
      (outcomeLaw prior observe (response prior observe (profile ()))).map
        (fun result => Node.done result.1 result.2) := by
  rw [InformationModel.runBehavioral, run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    initHistory, PMF.pure_bind, kernel, PMF.bind_map, outcomeLaw,
    PMF.map_bind, PMF.map_comp, Function.comp_def]

def site (state : State) (supported : state ∈ prior.support) :
    (model (Action := Action) prior observe).InformationSite () :=
  (model prior observe).informationSite () (decisionHistory prior state supported)
    (Classical.choice inferInstance) id rfl

theorem site_eq (original : (model (Action := Action) prior observe).InformationSite ()) :
    ∃ state supported, original = site (Action := Action) prior observe state supported := by
  obtain ⟨history, _, _, _⟩ := original.2
  have enabled := InformationModel.InformationSite.active (model prior observe) original history
  have known : Classified prior history.1 := classified prior history.1.trace
  rcases known with same | ⟨state, supported, same⟩ | ⟨state, supported, action, same⟩
  all_goals rw [same] at enabled
  all_goals try contradiction
  refine ⟨state, supported, Subtype.ext ?_⟩
  exact history.2.symm.trans (congrArg (fun history =>
    (model prior observe).infoOf () history.trace) same)

theorem history_at_site (original : (model (Action := Action) prior observe).InformationSite ())
    (history : (model prior observe).InformationHistory () original.1) :
    ∃ state supported, history.1 = decisionHistory (Action := Action) prior state supported ∧
      some (observe state) = original.1 := by
  have enabled := InformationModel.InformationSite.active (model prior observe) original history
  have known : Classified prior history.1 := classified prior history.1.trace
  rcases known with same | ⟨state, supported, same⟩ | ⟨state, supported, action, same⟩
  all_goals rw [same] at enabled
  all_goals try contradiction
  refine ⟨state, supported, same, ?_⟩
  have observed := history.2
  rw [same] at observed
  exact observed

theorem antichain : (model (Action := Action) prior observe).DecisionInformationAntichain := by
  intro who original first second joint legal node realized fuel reached
  cases who
  obtain ⟨left, leftPresent, leftEq, _⟩ := history_at_site prior observe original first
  obtain ⟨right, rightPresent, rightEq, _⟩ := history_at_site prior observe original second
  have increase := reached.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at increase
  rw [leftEq, rightEq] at increase
  change 1 + 1 ≤ 1 at increase
  omega

theorem reach_decision
    (profile : Profile (model (Action := Action) prior observe).behavioralSignature)
    (state : State) (supported : state ∈ prior.support) :
    (model prior observe).historyReachWeight profile
      (decisionHistory (Action := Action) prior state supported) = prior state := by
  classical
  change ((model prior observe).runBehavioralFrom profile 1 (arena prior).initHistory)
    (decisionHistory prior state supported) = _
  refine (pmf_map_apply_of_injective _ (state_injective prior) _).symm.trans ?_
  rw [run_states]
  simp only [Function.iterate_one, PMF.pure_bind, initHistory, kernel]
  exact pmf_map_apply_of_injective _ (fun _ _ same => Node.decision.inj same) _

def latent : Node State Action → State
  | .initial => prior.support_nonempty.choose
  | .decision state | .done state _ => state

def siteSignal (original : (model (Action := Action) prior observe).InformationSite ()) : Signal :=
  original.1.getD (observe prior.support_nonempty.choose)

theorem site_signal (original : (model (Action := Action) prior observe).InformationSite ()) :
    original.1 = some (siteSignal prior observe original) := by
  obtain ⟨state, supported, rfl⟩ := site_eq prior observe original
  rfl

theorem information_state (original : (model (Action := Action) prior observe).InformationSite ())
    (history : (model prior observe).InformationHistory () original.1) :
    history.1.state = .decision (latent prior history.1.state) ∧
      latent prior history.1.state ∈ prior.support ∧
        observe (latent prior history.1.state) = siteSignal prior observe original := by
  obtain ⟨state, supported, same, observed⟩ := history_at_site prior observe original history
  rw [same]
  refine ⟨rfl, supported, ?_⟩
  exact Option.some.inj (observed.trans (site_signal prior observe original))

theorem information_state_injective
    (original : (model (Action := Action) prior observe).InformationSite ()) :
    Function.Injective (fun history : (model prior observe).InformationHistory () original.1 =>
      latent prior history.1.state) := by
  intro first second same
  apply Subtype.ext
  apply state_injective prior
  rw [(information_state prior observe original first).1,
    (information_state prior observe original second).1]
  exact congrArg Node.decision same

variable [Finite Action]

def reference : (model (Action := Action) prior observe).BehavioralAssessment :=
  letI : Fintype Action := Fintype.ofFinite _
  .ofStrategy (fun _ => policy prior observe (fun _ => (PMF.uniformOfFintype _)))

theorem reference_mixed : (reference (Action := Action) prior observe).IsFullyMixed := by
  let : Fintype Action := Fintype.ofFinite _
  intro who original selected
  cases who
  obtain ⟨state, supported, rfl⟩ := site_eq prior observe original
  have legal := selected.2
  change selected.1.isSome = true at legal
  cases chosen : selected.1 with
  | none => simp [chosen] at legal
  | some action =>
      change selected ∈ ((PMF.uniformOfFintype Action).map
        (choice prior observe (observe state))).support
      rw [PMF.support_map]
      exact ⟨action, PMF.mem_support_uniformOfFintype action, Subtype.ext chosen.symm⟩

omit [Finite Action] in
theorem decision_reach_invariant
    (first second : Profile (model (Action := Action) prior observe).behavioralSignature)
    (original : (model (Action := Action) prior observe).InformationSite ())
    (history : (model prior observe).InformationHistory () original.1) :
    (model prior observe).historyReachWeight first history.1 =
      (model prior observe).historyReachWeight second history.1 := by
  obtain ⟨state, supported, same, _⟩ := history_at_site prior observe original history
  rw [same, reach_decision, reach_decision]

def assessment (original : Signal → PMF Action) :
    (model (Action := Action) prior observe).BehavioralAssessment where
  strategy _ := policy prior observe original
  belief := (InformationModel.bayesAssessment _ (reference prior observe).strategy
    (reference_mixed prior observe) (antichain prior observe)).belief

theorem assessment_consistent (original : Signal → PMF Action) :
    (assessment prior observe original).IsSequentiallyConsistent (antichain prior observe) := by
  have result := (model (Action := Action) prior observe).consistent_update_of_reach_invariant
    (reference prior observe) (reference_mixed prior observe) (antichain prior observe) ()
    (fun alternative who site history => by
      cases who
      exact decision_reach_invariant prior observe _ _ site history)
    (policy prior observe original)
  convert result using 1
  congr 1

variable [Finite State]

omit [Finite Action] in
theorem transition_support_finite {node : Node State Action} (joint : Unit → Option Action) :
    (transition prior node joint).support.Finite := by
  cases node with
  | initial =>
      rw [transition, PMF.support_map]
      exact (Set.toFinite _).image _
  | decision state => simp [transition]
  | done state action => simp [transition]

instance : Finite (arena (Action := Action) prior).History :=
  (reference_mixed (Action := Action) prior id).finite_history (bounded prior)
    (fun _ _ => Set.toFinite _) (fun draw => transition_support_finite prior draw.1)

instance : Fintype (arena (Action := Action) prior).History := Fintype.ofFinite _

instance (who : Unit) (original : (model (Action := Action) prior observe).InformationSite who) :
    Fintype ((model prior observe).InformationHistory who original.1) := by
  classical
  infer_instance

open Classical in
theorem sum_information [Fintype State] {Value : Type*} [AddCommMonoid Value]
    (original : (model (Action := Action) prior observe).InformationSite ())
    (f : State → Value) :
    (∑ history : (model prior observe).InformationHistory () original.1,
      f (latent prior history.1.state)) =
      ∑ state, if state ∈ prior.support ∧ observe state = siteSignal prior observe original
        then f state else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun history _ => latent prior history.1.state)
  · intro history _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (information_state prior observe original history).2
  · intro first _ second _ same
    exact information_state_injective prior observe original same
  · intro state member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
    refine ⟨⟨decisionHistory prior state member.1, ?_⟩, Finset.mem_univ _, rfl⟩
    change some (observe state) = original.1
    rw [member.2, site_signal]
  · intro history _
    rfl

theorem information_mass
    (profile : Profile (model (Action := Action) prior observe).behavioralSignature)
    (original : (model (Action := Action) prior observe).InformationSite ()) :
    (model prior observe).informationMass profile () original =
      prior.toOuterMeasure (observe ⁻¹' {siteSignal prior observe original}) := by
  classical
  let : Fintype State := Fintype.ofFinite _
  unfold InformationModel.informationMass
  have reach (history : (model prior observe).InformationHistory () original.1) :
      (model prior observe).historyReachWeight profile history.1 =
        prior (latent prior history.1.state) := by
    obtain ⟨state, supported, same, _⟩ := history_at_site prior observe original history
    rw [same, reach_decision]
    rfl
  simp_rw [reach]
  rw [tsum_fintype, sum_information, PMF.toOuterMeasure_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro state _
  by_cases present : state ∈ prior.support
  · by_cases same : observe state = siteSignal prior observe original <;>
      simp [present, same, Set.indicator]
  · have zero := (PMF.apply_eq_zero_iff _ _).mpr present
    simp [present, zero, Set.indicator]

omit [Finite State] in
theorem consistent_beliefs_unique
    (original : (model (Action := Action) prior observe).BehavioralAssessment)
    (consistent : original.IsSequentiallyConsistent (antichain prior observe)) :
    original.belief =
      (assessment prior observe (response prior observe (original.strategy ()))).belief := by
  obtain ⟨sequence, approximates, converges⟩ := consistent
  funext who site
  cases who
  have equal (n : Nat) : (sequence n).belief () site =
      (InformationModel.bayesAssessment _ (reference prior observe).strategy
        (reference_mixed prior observe) (antichain prior observe)).belief () site := by
    ext history
    rw [(approximates n).2 () site (InformationModel.informationMass_pos_of_fullSupport _ _
        (approximates n).1 () site) history,
      InformationModel.bayesAssessment, InformationModel.bayesBelief_apply]
    congr 1
    · exact decision_reach_invariant prior observe _ _ site history
    · unfold InformationModel.informationMass
      exact tsum_congr fun history => decision_reach_invariant prior observe _ _ site history
  ext history
  have converges := converges.2 () site history
  simp_rw [equal] at converges
  exact tendsto_nhds_unique converges tendsto_const_nhds

omit [Finite State] in
theorem consistent_eq_assessment
    (original : (model (Action := Action) prior observe).BehavioralAssessment)
    (consistent : original.IsSequentiallyConsistent (antichain prior observe)) :
    original = assessment prior observe (response prior observe (original.strategy ())) := by
  have beliefs := consistent_beliefs_unique prior observe original consistent
  cases original with
  | mk strategy belief =>
      have policies : strategy =
          fun _ => policy prior observe (response prior observe (strategy ())) := by
        funext who
        cases who
        exact (policy_response prior observe _).symm
      cases beliefs
      congr 1

def payoff (utility : State → Action → ℝ) : Node State Action → ℝ
  | .done state action => utility state action
  | _ => 0

theorem continuation_value (original : Signal → PMF Action)
    (site : (model (Action := Action) prior observe).InformationSite ())
    (utility : State → Action → ℝ)
    (alternative : (model prior observe).BehavioralPolicy ()) :
    ((assessment prior observe original).truncatedContinuationContext site
      (fun history => payoff utility history.state) 2).value alternative =
      localValue prior observe utility (siteSignal prior observe site)
        (response prior observe alternative (siteSignal prior observe site)) /
          (prior.toOuterMeasure (observe ⁻¹' {siteSignal prior observe site})).toReal := by
  classical
  let : Fintype State := Fintype.ofFinite _
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
      expect_bind_of_finite,
    expect_eq_sum]
  have run (history : (model prior observe).InformationHistory () site.1) :
      expect ((model prior observe).runBehavioralFrom
        (Profile.update (sig := (model prior observe).behavioralSignature)
          (assessment prior observe original).strategy () alternative) 2 history.1)
            (fun history => payoff utility history.state) =
        expect (response prior observe alternative (siteSignal prior observe site))
          (utility (latent prior history.1.state)) := by
    obtain ⟨state, supported, same, observed⟩ := history_at_site prior observe site history
    have signalEq := Option.some.inj (observed.trans (site_signal prior observe site))
    have law := congrArg (fun law => expect law (payoff utility))
      (run_decision prior observe
        (Profile.update (sig := (model prior observe).behavioralSignature)
          (assessment prior observe original).strategy () alternative) state supported)
    rw [same]
    change _ = expect (response prior observe alternative (siteSignal prior observe site))
      (utility state)
    simpa only [expect_map, Function.comp_def, Profile.update_same, signalEq, payoff] using law
  have mass (history : (model prior observe).InformationHistory () site.1) :
      (((assessment prior observe original).belief () site) history).toReal =
        (prior (latent prior history.1.state)).toReal /
          (prior.toOuterMeasure (observe ⁻¹' {siteSignal prior observe site})).toReal := by
    change (((InformationModel.bayesAssessment _ (reference prior observe).strategy
      (reference_mixed prior observe) (antichain prior observe)).belief () site) history).toReal = _
    rw [InformationModel.bayesAssessment, InformationModel.bayesBelief_apply,
      information_mass, ENNReal.toReal_div]
    obtain ⟨state, supported, same, _⟩ := history_at_site prior observe site history
    rw [same, reach_decision]
    rfl
  simp_rw [run, mass, div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_information prior observe site (fun state =>
    (prior state).toReal *
      expect (response prior observe alternative (siteSignal prior observe site)) (utility state))]
  congr 1
  rw [localValue, expect_eq_sum]
  apply Finset.sum_congr rfl
  intro state _
  by_cases present : state ∈ prior.support
  · by_cases same : observe state = siteSignal prior observe site <;> simp [present, same]
  · have zero := (PMF.apply_eq_zero_iff _ _).mpr present
    simp [present, zero]

theorem isSequentialEquilibrium_iff (original : Signal → PMF Action)
    (utility : State → Action → ℝ) :
    (assessment prior observe original).IsSequentialEquilibrium (antichain prior observe)
      (certificate prior) (fun _ history => payoff utility history.state) ↔
      IsBayesOptimal prior observe utility original := by
  classical
  rw [(assessment prior observe original).isSequentialEquilibrium_iff_truncated_of_bounded _ _
    (certificate prior) (bounded prior)]
  constructor
  · intro equilibrium
    refine ⟨fun _ => ResponseIntegrable.of_finite prior utility _, fun signal alternative _ => ?_⟩
    by_cases found : ∃ state ∈ prior.support, observe state = signal
    · obtain ⟨state, supported, observed⟩ := found
      have comparison :=
          (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _) fun _ _ =>
          (payoffIntegrable_of_finite _ _)).mp
        (equilibrium.1 () (site (Action := Action) prior observe state supported))
        (policy prior observe (fun _ => alternative)) (Set.mem_univ _)
      change ((assessment prior observe original).truncatedContinuationContext _ _ 2).value _ ≤
        ((assessment prior observe original).truncatedContinuationContext _ _ 2).value
          (policy prior observe original) at comparison
      rw [continuation_value, continuation_value, response_policy, response_policy] at comparison
      have signalEq : siteSignal prior observe
          (site (Action := Action) prior observe state supported) = signal := observed
      rw [signalEq] at comparison
      exact (div_le_div_iff_of_pos_right
        (toOuterMeasure_toReal_pos _ ⟨state, observed, supported⟩)).mp comparison
    · have zero (response : PMF Action) :
          localValue prior observe utility signal response = 0 := by
        rw [localValue]
        calc
          _ = expect prior (fun _ => (0 : ℝ)) := by
            apply expect_congr_on_support
            intro state supported
            have different : observe state ≠ signal := fun same => found ⟨state, supported, same⟩
            simp [different]
          _ = 0 := expect_constant _ _
      rw [zero, zero]
  · intro optimal
    refine ⟨?_, assessment_consistent prior observe original⟩
    intro who site
    cases who
    refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _) fun _ _ =>
        (payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
    change ((assessment prior observe original).truncatedContinuationContext _ _ 2).value _ ≤
      ((assessment prior observe original).truncatedContinuationContext _ _ 2).value
        (policy prior observe original)
    rw [continuation_value, continuation_value, response_policy]
    have positive :
        0 < (prior.toOuterMeasure (observe ⁻¹' {siteSignal prior observe site})).toReal := by
      rw [← information_mass prior observe (reference prior observe).strategy site]
      exact ENNReal.toReal_pos (InformationModel.informationMass_pos_of_fullSupport _ _
        (reference_mixed prior observe) () site).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
          (InformationModel.informationMass_le_one _ _ () site (antichain prior observe () site)))
    exact (div_le_div_iff_of_pos_right positive).mpr
      (optimal.2 _ _ (ResponseIntegrable.of_finite prior utility _))

theorem optimal_of_sequentialEquilibrium
    (original : (model (Action := Action) prior observe).BehavioralAssessment)
    (utility : State → Action → ℝ)
    (equilibrium : original.IsSequentialEquilibrium (antichain prior observe)
      (certificate prior) (fun _ history => payoff utility history.state)) :
    IsBayesOptimal prior observe utility (response prior observe (original.strategy ())) := by
  have same := congrArg
    (fun assessed : (model (Action := Action) prior observe).BehavioralAssessment =>
    assessed.IsSequentialEquilibrium (antichain prior observe)
      (certificate prior) (fun _ history => payoff utility history.state))
    (consistent_eq_assessment prior observe original equilibrium.2)
  exact (isSequentialEquilibrium_iff prior observe _ utility).mp (same.mp equilibrium)

def result {Fact : Type} (fact : State → Fact) : Node State Action → Fact × Action
  | .done state action => (fact state, action)
  | _ => (fact prior.support_nonempty.choose, Classical.choice inferInstance)

/-- The law of the retained fact and action at the end of play. -/
def observedLaw {Fact : Type} (fact : State → Fact)
    (original : (model (Action := Action) prior observe).BehavioralAssessment) :
    PMF (Fact × Action) :=
  ((model prior observe).runBehavioralTerminalFrom (certificate prior) original.strategy
    (arena prior).initHistory).map (fun history => result prior fact history.state)

omit [Finite Action] [Finite State] in
theorem observedLaw_eq {Fact : Type} (fact : State → Fact)
    (original : (model (Action := Action) prior observe).BehavioralAssessment) :
    observedLaw prior observe fact original =
      resultLaw prior observe fact (response prior observe (original.strategy ())) := by
  rw [observedLaw, InformationModel.runBehavioralTerminalFrom_initHistory _ _ _ (bounded prior)]
  calc
    _ = (((model prior observe).runBehavioral original.strategy 2).map History.state).map
        (result prior fact) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [run_initial, PMF.map_comp]
      rfl

/-- The complete initialized outcome laws of standard sequential equilibria
are exactly the Bayesian-optimal laws of the terminal decision experiment.
The left side quantifies over every protocol assessment, not only the supplied
canonical belief construction. -/
theorem equilibrium_law_iff {Fact : Type} (fact : State → Fact)
    (utility : Fact → Action → ℝ) (law : PMF (Fact × Action)) :
    (∃ original : (model (Action := Action) prior observe).BehavioralAssessment,
      original.IsSequentialEquilibrium (antichain prior observe)
        (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
            history.state) ∧
        observedLaw prior observe fact original = law) ↔
      ∃ original : Signal → PMF Action,
        IsBayesOptimal prior observe (fun state => utility (fact state)) original ∧
          resultLaw prior observe fact original = law := by
  constructor
  · rintro ⟨original, equilibrium, lawEq⟩
    exact ⟨response prior observe (original.strategy ()),
      optimal_of_sequentialEquilibrium prior observe original _ equilibrium,
      (observedLaw_eq prior observe fact original).symm.trans lawEq⟩
  · rintro ⟨original, optimal, lawEq⟩
    refine ⟨assessment prior observe original,
      (isSequentialEquilibrium_iff prior observe original _).mpr optimal, ?_⟩
    rw [observedLaw_eq]
    simpa only [assessment, response_policy] using lawEq

/-- Retaining the relevant fact preserves and reflects all sequential-
equilibrium outcome laws for every utility and every finite public action menu.
The concrete decision maker observes the complete latent state. -/
theorem sequentialEquilibrium_laws_iff {Fact : Type} (fact : State → Fact)
    (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (law : PMF (Fact × Action)) :
    (∃ original : (model (Action := Action) prior observe).BehavioralAssessment,
      original.IsSequentialEquilibrium (antichain prior observe)
        (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
            history.state) ∧
        observedLaw prior observe fact original = law) ↔
    (∃ original : (model (Action := Action) prior id).BehavioralAssessment,
      original.IsSequentialEquilibrium (antichain prior id)
        (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
            history.state) ∧
        observedLaw prior id fact original = law) := by
  rw [equilibrium_law_iff, equilibrium_law_iff]
  exact optimal_result_law_iff prior (Set.toFinite _) observe fact determines utility law

omit [Nonempty Action] [Finite Action] in
/-- Exact standard-SE classification for deterministic observation quotients
of a fully informed terminal decision. A finite fact-reporting menu already
tests necessity. Target assessments may depend on utilities: failed recovery
defeats outcome implementability, not just a particular strategy compiler. -/
theorem preserves_all_sequentialEquilibria_iff_determines
    {Fact : Type} [Finite Fact] [Nonempty Fact] (fact : State → Fact) :
    (∀ utility : Fact → Fact → ℝ,
      ∀ source : (model (Action := Fact) prior observe).BehavioralAssessment,
        source.IsSequentialEquilibrium (antichain prior observe)
          (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
              history.state) →
        ∃ target : (model (Action := Fact) prior id).BehavioralAssessment,
          target.IsSequentialEquilibrium (antichain prior id)
            (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
                history.state) ∧
          observedLaw prior id fact target = observedLaw prior observe fact source) ↔
      Determines prior observe fact := by
  rw [← preserves_all_optima_iff_determines prior (Set.toFinite _) observe fact]
  constructor
  · intro preserves utility source optimal
    obtain ⟨target, equilibrium, lawEq⟩ := preserves utility (assessment prior observe source)
      ((isSequentialEquilibrium_iff prior observe source _).mpr optimal)
    refine ⟨response prior id (target.strategy ()),
      optimal_of_sequentialEquilibrium prior id target _ equilibrium, ?_⟩
    rw [observedLaw_eq, observedLaw_eq] at lawEq
    simpa only [assessment, response_policy] using lawEq
  · intro preserves utility source equilibrium
    obtain ⟨target, optimal, lawEq⟩ := preserves utility
      (response prior observe (source.strategy ()))
      (optimal_of_sequentialEquilibrium prior observe source _ equilibrium)
    refine ⟨assessment prior id target,
      (isSequentialEquilibrium_iff prior id target _).mpr optimal, ?_⟩
    rw [observedLaw_eq, observedLaw_eq]
    simpa only [assessment, response_policy] using lawEq

end Protocol
end GameTheory.DecisionExperiment
