/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.RestrictionExtension
import GameTheoryExtensions.Analysis.Protocol.SequentialExistence

/-! # Enforcing a restriction with a new opponent continuation

The source gives Alice only the action `stay`, ending with payoff zero.
The target also allows `leave`, after which Bob chooses a Boolean response.
Both players prefer Bob's `true` response. Alice pays a persistent sanction
after leaving; Bob does not. Bob's new decision is therefore a genuine
continuation requiring rational completion, even though equilibrium play stays.

The forced source action deliberately aligns the decision clock and active
player with the target. This test does not silently identify an absent source
opportunity with a target decision.
-/

noncomputable section

namespace GameTheoryExtensionsTests.RestrictionEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive State where
  | start
  | response
  | done (answer : Option Bool)
  deriving DecidableEq, Fintype

def terminal : State → Prop
  | .done _ => True
  | _ => False

instance (state : State) : Decidable (terminal state) := by
  cases state <;> dsimp [terminal] <;> infer_instance

def active : State → Bool → Prop
  | .start, who => who = false
  | .response, who => who = true
  | .done _, _ => False

def available (unrestricted : Bool) (state : State) (who : Bool) : Set Bool :=
  if state = .start ∧ who = false ∧ unrestricted = false then {false} else Set.univ

def transition (state : State) (joint : Bool → Option Bool) : FinDist State :=
  match state with
  | .start => FinDist.pure (if (joint false).getD false then .response else .done none)
  | .response => FinDist.pure (.done (some ((joint true).getD false)))
  | .done answer => FinDist.pure (.done answer)

@[reducible] def arena (unrestricted : Bool) : ExecutionProtocol Bool where
  State := State
  Action _ := Bool
  init := .start
  active := active
  available := available unrestricted
  terminal := terminal
  step state joint := transition state joint.1
  progress state _ := by
    classical
    refine ⟨fun who => if active state who then some false else none, ?_⟩
    intro who
    by_cases enabled : active state who
    · simp only [enabled, ↓reduceIte, true_and]
      unfold available
      split <;> simp
    · simp [enabled]

def joint (who action : Bool) : Bool → Option Bool :=
  fun other => if other = who then some action else none

theorem stay_legal (unrestricted : Bool) :
    (arena unrestricted).Legal .start (joint false false) := by
  constructor
  · simp [terminal]
  · intro who
    cases who <;> cases unrestricted <;> simp [arena, active, available, joint]

theorem leave_legal (unrestricted : Bool) (allowed : unrestricted = true) :
    (arena unrestricted).Legal .start (joint false true) := by
  subst unrestricted
  constructor
  · simp [terminal]
  · intro who
    cases who <;> simp [arena, active, available, joint]

theorem response_legal (unrestricted answer : Bool) :
    (arena unrestricted).Legal .response (joint true answer) := by
  constructor
  · simp [terminal]
  · intro who
    cases who <;> simp [arena, active, available, joint]

def stayHistory (unrestricted : Bool) : (arena unrestricted).History :=
  (arena unrestricted).initHistory.extend (stay_legal unrestricted)
    (FinDist.mem_support_pure.mpr rfl)

def responseHistory (unrestricted : Bool) (allowed : unrestricted = true) :
    (arena unrestricted).History :=
  (arena unrestricted).initHistory.extend (leave_legal unrestricted allowed)
    (FinDist.mem_support_pure.mpr rfl)

def doneHistory (unrestricted : Bool) (allowed : unrestricted = true) (answer : Bool) :
    (arena unrestricted).History :=
  (responseHistory unrestricted allowed).extend (response_legal unrestricted answer)
    (FinDist.mem_support_pure.mpr rfl)

theorem start_joint (unrestricted : Bool) (choices : Bool → Option Bool)
    (legal : (arena unrestricted).Legal .start choices) :
    ∃ answer, choices = joint false answer ∧ (answer = true → unrestricted = true) := by
  obtain ⟨answer, selected⟩ := LegalOption.exists_eq_some_of_active (E := arena unrestricted)
    (choices false) ((arena unrestricted).legalOption_of_legal legal false) rfl
  refine ⟨answer, ?_, ?_⟩
  · funext who
    cases who
    · simpa [joint] using selected
    · have idle := LegalOption.eq_none_of_inactive (E := arena unrestricted) (choices true)
        ((arena unrestricted).legalOption_of_legal legal true) (by simp [active])
      simpa [joint] using idle
  · intro trueAnswer
    have permitted := ((arena unrestricted).legalOption_of_legal legal false)
    rw [selected, trueAnswer] at permitted
    cases unrestricted <;> simp_all [LegalOption, available]

theorem response_joint (unrestricted : Bool) (choices : Bool → Option Bool)
    (legal : (arena unrestricted).Legal .response choices) :
    ∃ answer, choices = joint true answer := by
  obtain ⟨answer, selected⟩ := LegalOption.exists_eq_some_of_active (E := arena unrestricted)
    (choices true) ((arena unrestricted).legalOption_of_legal legal true) rfl
  refine ⟨answer, ?_⟩
  funext who
  cases who
  · have idle := LegalOption.eq_none_of_inactive (E := arena unrestricted) (choices false)
      ((arena unrestricted).legalOption_of_legal legal false) (by simp [active])
    simpa [joint] using idle
  · simpa [joint] using selected

def Classified (unrestricted : Bool) (history : (arena unrestricted).History) : Prop :=
  history = (arena unrestricted).initHistory ∨ history = stayHistory unrestricted ∨
    (∃ allowed, history = responseHistory unrestricted allowed) ∨
      ∃ allowed answer, history = doneHistory unrestricted allowed answer

theorem classified_step (unrestricted : Bool) (history : (arena unrestricted).History)
    (known : Classified unrestricted history) (choices : Bool → Option Bool)
    (legal : (arena unrestricted).Legal history.state choices) (next : State)
    (reached : next ∈ ((arena unrestricted).step history.state ⟨choices, legal⟩).support) :
    Classified unrestricted (history.extend legal reached) := by
  rcases known with rfl | rfl | ⟨allowed, rfl⟩ | ⟨allowed, answer, rfl⟩
  · obtain ⟨answer, rfl, permitted⟩ := start_joint unrestricted choices legal
    cases answer
    · cases FinDist.mem_support_pure.mp reached
      exact Or.inr (Or.inl rfl)
    · cases FinDist.mem_support_pure.mp reached
      exact Or.inr (Or.inr (Or.inl ⟨permitted rfl, rfl⟩))
  · exact (legal.1 trivial).elim
  · obtain ⟨answer, rfl⟩ := response_joint unrestricted choices legal
    cases FinDist.mem_support_pure.mp reached
    exact Or.inr (Or.inr (Or.inr ⟨allowed, answer, rfl⟩))
  · exact (legal.1 trivial).elim

theorem classified (unrestricted : Bool) :
    ∀ {state} (trace : (arena unrestricted).Trace state), Classified unrestricted ⟨state, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend prior choices legal reached =>
      classified_step unrestricted _ (classified unrestricted prior) choices legal _ reached

theorem state_injective (unrestricted : Bool) :
    Function.Injective (History.state (E := arena unrestricted)) := by
  intro first second same
  have firstKnown : Classified unrestricted first := classified unrestricted first.trace
  have secondKnown : Classified unrestricted second := classified unrestricted second.trace
  rcases firstKnown with rfl | rfl | ⟨allowed, rfl⟩ |
    ⟨allowed, answer, rfl⟩ <;>
    rcases secondKnown with rfl | rfl | ⟨allowed', rfl⟩ |
      ⟨allowed', answer', rfl⟩
  all_goals first | rfl | cases same <;> rfl

instance (unrestricted : Bool) : Finite (arena unrestricted).History :=
  Finite.of_injective _ (state_injective unrestricted)

instance (unrestricted : Bool) : Fintype (arena unrestricted).History := Fintype.ofFinite _

@[reducible] def signals (unrestricted : Bool) : InfoSignals (arena unrestricted) where
  PublicSignal := State
  PrivateSignal _ := Unit
  initialPublic := .start
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := State
  initInfo _ _ seen := seen
  pushInfo _ _ _ _ seen := seen

theorem info_state (unrestricted who : Bool) :
    ∀ {state} (trace : (arena unrestricted).Trace state),
      (signals unrestricted).infoOf who trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def model (unrestricted : Bool) : InformationModel (arena unrestricted) where
  toInfoSignals := signals unrestricted
  menu who state := {choice | LegalOption (E := arena unrestricted) state who choice}
  menu_adequate who state trace choice := by rw [info_state]; rfl

instance (unrestricted who : Bool) (site : (model unrestricted).InformationSite who) :
    Fintype ((model unrestricted).InformationHistory who site.1) := by
  classical
  infer_instance

theorem perfectRecall (unrestricted : Bool) : (model unrestricted).PerfectRecall := by
  intro who first second traceFirst traceSecond equal
  have same : (⟨first, traceFirst⟩ : (arena unrestricted).History) = ⟨second, traceSecond⟩ :=
    state_injective unrestricted (by simpa only [info_state] using equal)
  cases same
  rfl

theorem source_classified (history : (arena false).History) :
    history = (arena false).initHistory ∨ history = stayHistory false := by
  have known : Classified false history := classified false history.trace
  rcases known with initial | stayed | ⟨impossible, _⟩ | ⟨impossible, _, _⟩
  · exact Or.inl initial
  · exact Or.inr stayed
  · cases impossible
  · cases impossible

def embedHistory (history : (arena false).History) : (arena true).History :=
  if history.state = .start then (arena true).initHistory else stayHistory true

theorem embedHistory_state (history : (arena false).History) :
    (embedHistory history).state = history.state := by
  rcases source_classified history with rfl | rfl <;>
    simp [embedHistory, stayHistory, joint]

def historyEmbedding : (arena false).History ↪ (arena true).History where
  toFun := embedHistory
  inj' := by
    intro first second same
    apply state_injective false
    simpa only [embedHistory_state] using congrArg History.state same

def choiceEmbedding (who : Bool) (info : State) :
    (model false).Choice who info ↪ (model true).Choice who info where
  toFun choice := ⟨choice.1, by
    have allowed := choice.2
    change LegalOption (arena false) info who choice.1 at allowed
    change LegalOption (arena true) info who choice.1
    cases value : choice.1 with
    | none => simpa only [value, LegalOption] using allowed
    | some action =>
        rw [value] at allowed
        exact ⟨allowed.1, by simp [available]⟩⟩
  inj' := by
    intro first second same
    exact Subtype.ext (congrArg (fun choice : (model true).Choice who info => choice.1) same)

theorem localStep_state (unrestricted : Bool) (history : (arena unrestricted).History)
    (choices : ∀ who, (model unrestricted).Choice who
      ((model unrestricted).infoOf who history.trace)) :
    ((model unrestricted).localStep history choices).map History.state =
      if terminal history.state then FinDist.pure history.state else
        transition history.state (fun who => (choices who).1) := by
  classical
  by_cases stopped : terminal history.state
  · simp only [InformationModel.localStep, stopped, ↓reduceDIte, ↓reduceIte, FinDist.map_pure]
  · simp only [InformationModel.localStep, stopped, ↓reduceDIte, ↓reduceIte,
      FinDist.map_bindOnSupport, FinDist.map_pure, History.extend_state]
    calc
      _ = (transition history.state (fun who => (choices who).1)).bind FinDist.pure :=
        FinDist.bindOnSupport_eq_bind_of_eq_on_support (fun _ _ => rfl)
      _ = _ := FinDist.bind_pure _

def restriction : (model false).ActionRestriction (model true) where
  history := historyEmbedding
  information _ := Function.Embedding.refl _
  choice := choiceEmbedding
  initial := by simp [historyEmbedding, embedHistory]
  length history := by
    rcases source_classified history with rfl | rfl <;>
      simp [historyEmbedding, embedHistory, stayHistory, joint] <;> rfl
  terminal history := by
    change terminal (embedHistory history).state ↔ terminal history.state
    rw [embedHistory_state]
  active history who := by
    change active (embedHistory history).state who ↔ active history.state who
    rw [embedHistory_state]
  observed who history := by
    change (signals true).infoOf who (embedHistory history).trace =
      (signals false).infoOf who history.trace
    rw [info_state, info_state, embedHistory_state]
  step history choices := by
    apply FinDist.map_injective (state_injective true)
    rw [FinDist.map_comp]
    have sameState : History.state ∘ historyEmbedding = History.state :=
      funext embedHistory_state
    rw [sameState, localStep_state, localStep_state]
    rcases source_classified history with rfl | rfl <;>
      simp [historyEmbedding, embedHistory, terminal, stayHistory, transition, joint,
        choiceEmbedding]; rfl

def historyDepth : State → Nat
  | .start => 0
  | .response => 1
  | .done none => 1
  | .done (some _) => 2

theorem history_length (unrestricted : Bool) (history : (arena unrestricted).History) :
    history.trace.length = historyDepth history.state := by
  have known : Classified unrestricted history := classified unrestricted history.trace
  rcases known with rfl | rfl | ⟨allowed, rfl⟩ | ⟨allowed, answer, rfl⟩ <;> rfl

theorem bounded (unrestricted : Bool) : (arena unrestricted).BoundedHorizon 2 := by
  intro state trace enough
  have length := history_length unrestricted ⟨state, trace⟩
  change trace.length = historyDepth state at length
  rw [length] at enough
  cases state <;> simp_all [historyDepth, terminal]

def siteDepth (unrestricted who : Bool) (_ : (model unrestricted).InformationSite who) : Nat :=
  if who then 1 else 0

theorem clock (unrestricted who : Bool) (site : (model unrestricted).InformationSite who) :
    InformationModel.InformationSite.CommonDepth (model unrestricted) site
      (siteDepth unrestricted who site) := by
  intro history
  have acts := InformationModel.InformationSite.active (model unrestricted) site history
  rw [history_length]
  cases state : history.1.state <;> cases who <;>
    simp_all [arena, active, historyDepth, siteDepth]

theorem source_site (who : Bool) (site : (model false).InformationSite who) :
    who = false ∧ site.1 = .start := by
  obtain ⟨history, running, _⟩ := site.2
  rcases source_classified history.1 with initial | stayed
  · have acts := InformationModel.InformationSite.active (model false) site history
    have same : site.1 = .start := history.2.symm.trans (by rw [initial]; rfl)
    refine ⟨?_, same⟩
    rw [initial] at acts
    exact acts
  · exact (running (by rw [stayed]; trivial)).elim

def defaultChoice (unrestricted who : Bool) (info : State) :
    (model unrestricted).Choice who info := by
  classical
  refine ⟨if active info who then some false else none, ?_⟩
  by_cases acts : active info who
  · change LegalOption (arena unrestricted) info who _
    simp only [acts, ↓reduceIte, LegalOption, true_and]
    unfold available
    split <;> simp
  · change LegalOption (arena unrestricted) info who _
    simp only [acts, ↓reduceIte, LegalOption, not_false_eq_true]

instance (unrestricted who : Bool) (info : State) :
    Nonempty ((model unrestricted).Choice who info) := ⟨defaultChoice unrestricted who info⟩

instance (unrestricted who : Bool) (info : State) :
    Fintype ((model unrestricted).Choice who info) := by
  classical
  infer_instance

def reference (unrestricted : Bool) : (model unrestricted).BehavioralAssessment :=
  InformationModel.BehavioralAssessment.ofStrategy fun _ _ => FinDist.uniformOfFintype

theorem reference_mixed (unrestricted : Bool) : (reference unrestricted).IsFullyMixed := by
  intro who site choice
  exact FinDist.mem_support_uniformOfFintype choice

def base (history : (arena true).History) (_ : Bool) : ℝ :=
  if history.state = .done (some true) then 1 else 0

def charge (history : (arena true).History) (who : Bool) : ℝ :=
  if who then 0 else match history.state with
    | .response | .done (some _) => 1
    | _ => 0

theorem matching (history : (arena false).History) (who : Bool) :
    base (restriction.history history) who = 0 := by
  change (if (embedHistory history).state = .done (some true) then (1 : ℝ) else 0) = 0
  rw [embedHistory_state]
  rcases source_classified history with rfl | rfl <;> rfl

theorem clean (history : (arena false).History) (who : Bool) :
    charge (restriction.history history) who = 0 := by
  change (if who then 0 else match (embedHistory history).state with
    | .response | .done (some _) => (1 : ℝ)
    | _ => 0) = 0
  rw [embedHistory_state]
  rcases source_classified history with rfl | rfl <;> cases who <;> rfl

theorem exists_source_equilibrium :
    ∃ source : (model false).BehavioralAssessment,
      source.IsSequentialEquilibriumFor
        ((model false).decisionInformationAntichain_of_perfectRecall (perfectRecall false))
        (fun who site => source.continuationContext site (fun _ => 0)
          (2 - siteDepth false who site)) := by
  apply (model false).exists_sequential_equilibrium (reference false) (reference_mixed false)
    ((model false).decisionRecall_of_perfectRecall (perfectRecall false))
    2 (fun _ _ => 0) (siteDepth false) (clock false)
  intro who site
  cases who <;> simp [siteDepth]

theorem localStep_leave (choices : ∀ who, (model true).Choice who
    ((model true).infoOf who (arena true).initHistory.trace))
    (leaves : (choices false).1 = some true) :
    (model true).localStep (arena true).initHistory choices =
      FinDist.pure (responseHistory true rfl) := by
  apply FinDist.map_injective (state_injective true)
  rw [localStep_state, FinDist.map_pure]
  simp [terminal, transition, leaves, responseHistory, joint]

theorem run_root_leave (profile : ∀ who, (model true).BehavioralPolicy who)
    (action : (model true).Choice false .start) (leaves : action.1 = some true) :
    (model true).runBehavioralFrom
        (Profile.update (sig := (model true).behavioralSignature) profile false
          ((profile false).commit .start action)) 1 (arena true).initHistory =
      FinDist.pure (responseHistory true rfl) := by
  let played := Profile.update (sig := (model true).behavioralSignature) profile false
    ((profile false).commit .start action)
  rw [(model true).runBehavioralFrom_succ_localStep]
  change ((FinDist.pi fun who => played who .start).bind
    ((model true).localStep (arena true).initHistory)).bind FinDist.pure = _
  rw [FinDist.bind_pure]
  calc
    _ = (FinDist.pi fun who => played who .start).bind
        (fun _ => FinDist.pure (responseHistory true rfl)) := by
      apply FinDist.bind_congr
      intro choices supported
      have own := FinDist.mem_support_pi.mp supported false
      simp only [played, Profile.update_same, InformationModel.BehavioralPolicy.commit_self] at own
      have selected : choices false = action := FinDist.mem_support_pure.mp own
      exact localStep_leave choices (selected ▸ leaves)
    _ = _ := FinDist.bind_const _ _

theorem response_charge (profile : ∀ who, (model true).BehavioralPolicy who) :
    ((model true).runBehavioralFrom profile 1 (responseHistory true rfl)).expect
      (fun history => charge history false) = 1 := by
  rw [(model true).runBehavioralFrom_succ_localStep]
  simp only [InformationModel.runBehavioralFrom, runRandomizedFor_zero,
    FinDist.expect_bind, FinDist.expect_pure]
  calc
    _ = (FinDist.pi fun who => profile who
        ((model true).infoOf who (responseHistory true rfl).trace)).expect (fun _ => 1) := by
      apply FinDist.expect_congr
      intro choices _
      let cost : State → ℝ := fun state => match state with
        | .response | .done (some _) => 1
        | _ => 0
      change ((model true).localStep (responseHistory true rfl) choices).expect
        (fun history => cost history.state) = 1
      rw [← FinDist.expect_map, localStep_state]
      simp [responseHistory, terminal, transition, cost, joint, FinDist.expect_pure]
    _ = _ := FinDist.expect_const _ _

theorem leave_collection (profile : ∀ who, (model true).BehavioralPolicy who)
    (action : (model true).Choice false .start) (leaves : action.1 = some true) :
    ((model true).runBehavioralFrom
      (Profile.update (sig := (model true).behavioralSignature) profile false
        ((profile false).commit .start action)) 2 (arena true).initHistory).expect
        (fun history => charge history false) = 1 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, (model true).runBehavioralFrom_add,
    run_root_leave profile action leaves, FinDist.pure_bind]
  exact response_charge _

theorem collection (profile : ∀ who, (model true).BehavioralPolicy who) (who : Bool)
    (site : (model false).InformationSite who)
    (action : (model true).Choice who (restriction.site who site).1)
    (forbidden : action ∉ Set.range (restriction.choice who site.1))
    (history : (model false).InformationHistory who site.1) :
    (1 : ℝ) ≤ ((model true).runBehavioralFrom
      (Profile.update (sig := (model true).behavioralSignature) profile who
        ((profile who).commit (restriction.site who site).1 action))
      (2 - siteDepth true who (restriction.site who site))
      (restriction.history history.1)).expect (fun final => charge final who) := by
  obtain ⟨rfl, atRoot⟩ := source_site who site
  rcases site with ⟨info, site⟩
  dsimp only at atRoot
  subst info
  have initial : history.1 = (arena false).initHistory := by
    apply state_injective false
    change history.1.state = .start
    have observed := history.2
    simpa only [info_state] using observed
  have activeChoice := action.2
  change LegalOption (arena true) .start false action.1 at activeChoice
  obtain ⟨value, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena true)
    action.1 activeChoice rfl
  have leaves : action.1 = some true := by
    cases value
    · apply False.elim
      apply forbidden
      refine ⟨⟨some false, ?_⟩, ?_⟩
      · exact ⟨rfl, by simp [available]⟩
      · apply Subtype.ext
        exact chosen.symm
    · exact chosen
  change (1 : ℝ) ≤ ((model true).runBehavioralFrom
    (Profile.update (sig := (model true).behavioralSignature) profile false
      ((profile false).commit .start action)) 2 (embedHistory history.1)).expect _
  rw [initial, show embedHistory (arena false).initHistory = (arena true).initHistory by rfl,
    leave_collection profile action leaves]

theorem source_initialized (profile : ∀ who, (model false).BehavioralPolicy who) :
    (model false).runBehavioral profile 2 = FinDist.pure (stayHistory false) := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro final supported
  have stopped := (model false).runBehavioralFrom_terminal_of_bound profile (bounded false)
    (arena false).initHistory final supported
  rcases source_classified final with rfl | rfl
  · exact stopped.elim
  · rfl

def bobSite : (model true).InformationSite true :=
  (model true).informationSite true (responseHistory true rfl) false
    (by simp [responseHistory, terminal, joint])
    (by exact ⟨rfl, Set.mem_univ _⟩)

theorem new_opponent_site : ¬ restriction.Retained true bobSite.1 := by
  rintro ⟨sourceSite, _⟩
  have impossible := (source_site true sourceSite).1
  cases impossible

/-- One fixed finite deposit works for every actual source SE. The generic
theorem constructs a standard target SE, including Bob's new off-path site;
the completed initialized outcome and both net payoffs remain exactly zero. -/
theorem every_source_equilibrium_preserved (deposit : ℝ) (large : 1 ≤ deposit)
    (source : (model false).BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibriumFor
      ((model false).decisionInformationAntichain_of_perfectRecall (perfectRecall false))
      (fun who site => source.continuationContext site (fun _ => 0)
        (2 - siteDepth true who (restriction.site who site)))) :
    ∃ target : (model true).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((model true).decisionInformationAntichain_of_perfectRecall (perfectRecall true))
        (fun who site => target.continuationContext site
          (fun history => base history who - charge history who * deposit)
          (2 - siteDepth true who site)) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (model true).runBehavioral target.strategy 2 = FinDist.pure (stayHistory true) ∧
      ((model true).runBehavioral target.strategy 2).map (fun history =>
        (history.state, fun who => base history who - charge history who * deposit)) =
          FinDist.pure (.done none, fun _ : Bool => (0 : ℝ)) := by
  obtain ⟨target, equilibrium, agrees, _, law, _, _⟩ :=
    restriction.sequential_equilibrium_extends
      ((model false).decisionInformationAntichain_of_perfectRecall (perfectRecall false))
      (reference true) (reference_mixed true)
      ((model true).decisionRecall_of_perfectRecall (perfectRecall true)) 2 (bounded true)
      (siteDepth true) (clock true) (fun _ _ => 0) base charge matching clean
      (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => deposit)
      (fun _ => le_trans (by norm_num) large) (fun _ _ => le_rfl)
      (fun history _ => by unfold base; split <;> norm_num)
      (fun _ => by linarith) collection source sourceEquilibrium
  have initialized : (model true).runBehavioral target.strategy 2 =
      FinDist.pure (stayHistory true) := by
    rw [source_initialized, FinDist.map_pure] at law
    exact law.symm
  refine ⟨target, equilibrium, agrees, initialized, ?_⟩
  rw [initialized, FinDist.map_pure]
  congr 1
  apply Prod.ext
  · rfl
  · funext who
    cases who <;> simp [base, charge, stayHistory, joint]

/-- The preservation hypothesis is inhabited, and the fixed deposit one
produces an actual target equilibrium with the source's zero-payoff outcome. -/
theorem deposit_one_implements :
    ∃ target : (model true).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((model true).decisionInformationAntichain_of_perfectRecall (perfectRecall true))
        (fun who site => target.continuationContext site
          (fun history => base history who - charge history who)
          (2 - siteDepth true who site)) ∧
      (model true).runBehavioral target.strategy 2 = FinDist.pure (stayHistory true) := by
  obtain ⟨source, sourceEquilibrium⟩ := exists_source_equilibrium
  obtain ⟨target, equilibrium, _, initialized, _⟩ :=
    every_source_equilibrium_preserved 1 le_rfl source sourceEquilibrium
  exact ⟨target, by simpa only [mul_one] using equilibrium, initialized⟩

end GameTheoryExtensionsTests.RestrictionEnforcement
