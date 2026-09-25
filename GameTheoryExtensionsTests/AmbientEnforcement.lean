/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion
import GameTheoryExtensions.Protocol.BehavioralContinuation
import GameTheoryExtensions.Protocol.StateKernel

/-! # Optional communication before an unchanged guessing game

Chance gives Alice a private fair bit. Bob always guesses it. The target adds
one optional ambient disclosure by Alice before Bob's guess; the source passes
that stage silently with no player action. Disclosure authenticates the bit.
Both players receive the correctness reward. An automatic fine, considered in
the assessment experiment, can apply to Alice's ambient disclosure alone.

This finite protocol is an abstract enforcement experiment, not a runtime
implementation or a claim that private disclosure can be detected on a ledger.
-/

noncomputable section

namespace GameTheoryExtensionsTests.AmbientEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive State where
  | initial
  | alice (bit : Bool)
  | bob (bit disclosed : Bool)
  | done (bit disclosed guess : Bool)
  deriving DecidableEq, Fintype

def actor (ambient : Bool) : State → Option Bool
  | .alice _ => if ambient then some false else none
  | .bob _ _ => some true
  | _ => none

def terminal : State → Prop
  | .done _ _ _ => True
  | _ => False

def transition (ambient : Bool) (state : State) (joint : Bool → Option Bool) : FinDist State :=
  match state with
  | .initial => (FinDist.uniformOfFintype (α := Bool)).map State.alice
  | .alice bit => FinDist.pure (.bob bit (ambient && (joint false).getD false))
  | .bob bit disclosed => FinDist.pure (.done bit disclosed ((joint true).getD false))
  | .done bit disclosed guess => FinDist.pure (.done bit disclosed guess)

@[reducible] def arena (ambient : Bool) : ExecutionProtocol Bool where
  State := State
  Action _ := Bool
  init := .initial
  active state who := actor ambient state = some who
  available _ _ := Set.univ
  terminal := terminal
  step state joint := transition ambient state joint.1
  progress state _ := by
    refine ⟨fun who => if actor ambient state = some who then some false else none, ?_⟩
    intro who
    by_cases acts : actor ambient state = some who <;> simp [acts]

def depth : State → Nat
  | .initial => 0
  | .alice _ => 1
  | .bob _ _ => 2
  | .done _ _ _ => 3

theorem history_length (ambient : Bool) : ∀ {state} (trace : (arena ambient).Trace state),
    trace.length = depth state
  | _, .start => rfl
  | _, .extend (source := before) prior joint legal reached => by
      have earlier := history_length ambient prior
      cases before with
      | initial =>
          obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ reached
          simpa only [Trace.length, depth] using congrArg (· + 1) earlier
      | alice bit =>
          cases FinDist.mem_support_pure.mp reached
          simpa only [Trace.length, depth] using congrArg (· + 1) earlier
      | bob bit disclosed =>
          cases FinDist.mem_support_pure.mp reached
          simpa only [Trace.length, depth] using congrArg (· + 1) earlier
      | done bit disclosed guess => exact (legal.1 trivial).elim

theorem bounded (ambient : Bool) : (arena ambient).BoundedHorizon 3 := by
  intro state trace enough
  rw [history_length ambient trace] at enough
  cases state <;> simp_all [depth, terminal]

theorem single (ambient : Bool) : ∀ state {first second},
    (arena ambient).active state first → (arena ambient).active state second → first = second := by
  intro state first second left right
  exact Option.some.inj (left.symm.trans right)

def observation (who : Bool) : State → Option (Option Bool)
  | .alice bit => if who then none else some (some bit)
  | .bob bit disclosed => if who then some (if disclosed then some bit else none) else none
  | _ => none

@[reducible] def signals (ambient : Bool) : InfoSignals (arena ambient) where
  PublicSignal := Unit
  PrivateSignal _ := Option (Option Bool)
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := observation who event.target
  InfoState _ := Option (Option Bool)
  initInfo _ secret _ := secret
  pushInfo _ _ _ secret _ := secret

theorem info_state (ambient who : Bool) : ∀ {state} (trace : (arena ambient).Trace state),
    (signals ambient).infoOf who trace = observation who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def decisionInfo (ambient who : Bool) (info : Option (Option Bool)) : Bool :=
  (ambient || who) && info.isSome

@[reducible] def model (ambient : Bool) : InformationModel (arena ambient) where
  toInfoSignals := signals ambient
  menu who info := {choice | choice.isSome = decisionInfo ambient who info}
  menu_adequate who state trace choice := by
    rw [info_state]
    cases ambient <;> cases state <;> cases who <;> cases choice <;>
      simp [decisionInfo, observation, LegalOption, arena, actor]

def aliceJoint (ambient disclose : Bool) : Bool → Option Bool :=
  fun who => if ambient && !who then some disclose else none

def bobJoint (guess : Bool) : Bool → Option Bool := fun who => if who then some guess else none

theorem initial_legal (ambient : Bool) :
    (arena ambient).Legal .initial (fun _ => none) := by
  exact ⟨id, fun _ => by simp [actor]⟩

theorem alice_legal (ambient bit disclose : Bool) :
    (arena ambient).Legal (.alice bit) (aliceJoint ambient disclose) := by
  constructor
  · simp [terminal]
  · intro who; cases ambient <;> cases who <;> simp [arena, actor, aliceJoint]

theorem bob_legal (ambient bit disclosed guess : Bool) :
    (arena ambient).Legal (.bob bit disclosed) (bobJoint guess) := by
  constructor
  · simp [terminal]
  · intro who; cases who <;> simp [arena, actor, bobJoint]

def aliceHistory (ambient bit : Bool) : (arena ambient).History :=
  (arena ambient).initHistory.extend (target := .alice bit) (initial_legal ambient) (by
    change State.alice bit ∈ ((FinDist.uniformOfFintype (α := Bool)).map State.alice).support
    rw [FinDist.support_map]
    exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩)

def bobHistory (ambient bit disclose : Bool) : (arena ambient).History :=
  (aliceHistory ambient bit).extend (alice_legal ambient bit disclose)
    (FinDist.mem_support_pure.mpr rfl)

def guessHistory (ambient bit disclose guess : Bool) : (arena ambient).History :=
  (bobHistory ambient bit disclose).extend
    (bob_legal ambient bit (ambient && disclose) guess) (FinDist.mem_support_pure.mpr rfl)

theorem initial_joint (ambient : Bool) (joint : Bool → Option Bool)
    (legal : (arena ambient).Legal .initial joint) : joint = fun _ => none := by
  funext who
  exact LegalOption.eq_none_of_inactive (E := arena ambient) (joint who)
    ((arena ambient).legalOption_of_legal legal who) (by simp [actor])

theorem alice_joint (ambient bit : Bool) (joint : Bool → Option Bool)
    (legal : (arena ambient).Legal (.alice bit) joint) :
    joint = aliceJoint ambient ((joint false).getD false) := by
  cases ambient
  · funext who
    exact LegalOption.eq_none_of_inactive (E := arena false) (joint who)
      ((arena false).legalOption_of_legal legal who) (by simp [actor])
  · obtain ⟨ask, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena true) (joint false)
      ((arena true).legalOption_of_legal legal false) rfl
    funext who
    cases who
    · simp [aliceJoint, chosen]
    · exact LegalOption.eq_none_of_inactive (E := arena true) (joint true)
        ((arena true).legalOption_of_legal legal true) (by simp [actor])

theorem bob_joint (ambient bit disclosed : Bool) (joint : Bool → Option Bool)
    (legal : (arena ambient).Legal (.bob bit disclosed) joint) :
    joint = bobJoint ((joint true).getD false) := by
  obtain ⟨guess, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena ambient) (joint true)
    ((arena ambient).legalOption_of_legal legal true) rfl
  funext who
  cases who
  · exact LegalOption.eq_none_of_inactive (E := arena ambient) (joint false)
      ((arena ambient).legalOption_of_legal legal false) (by simp [actor])
  · simp [bobJoint, chosen]

def Classified (ambient : Bool) (history : (arena ambient).History) : Prop :=
  history = (arena ambient).initHistory ∨ (∃ bit, history = aliceHistory ambient bit) ∨
    (∃ bit disclose, history = bobHistory ambient bit disclose) ∨
      ∃ bit disclose guess, history = guessHistory ambient bit disclose guess

theorem classified_step (ambient : Bool) (history : (arena ambient).History)
    (known : Classified ambient history) (joint : Bool → Option Bool)
    (legal : (arena ambient).Legal history.state joint) (target : State)
    (reached : target ∈ ((arena ambient).step history.state ⟨joint, legal⟩).support) :
    Classified ambient (history.extend legal reached) := by
  rcases known with rfl | ⟨bit, rfl⟩ | ⟨bit, disclose, rfl⟩ | ⟨bit, disclose, guess, rfl⟩
  · have same := initial_joint ambient joint legal
    subst joint
    obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ reached
    exact Or.inr (Or.inl ⟨bit, rfl⟩)
  · have same := alice_joint ambient bit joint legal
    obtain ⟨disclose, same⟩ : ∃ disclose, joint = aliceJoint ambient disclose :=
      ⟨_, same⟩
    subst joint
    cases FinDist.mem_support_pure.mp reached
    exact Or.inr (Or.inr (Or.inl ⟨bit, disclose, rfl⟩))
  · have same := bob_joint ambient bit (ambient && disclose) joint legal
    obtain ⟨guess, same⟩ : ∃ guess, joint = bobJoint guess := ⟨_, same⟩
    subst joint
    cases FinDist.mem_support_pure.mp reached
    exact Or.inr (Or.inr (Or.inr ⟨bit, disclose, guess, rfl⟩))
  · exact (legal.1 trivial).elim

theorem classified (ambient : Bool) : ∀ {state} (trace : (arena ambient).Trace state),
    Classified ambient ⟨state, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend prior joint legal reached =>
      classified_step ambient _ (classified ambient prior) joint legal _ reached

def historyOfState (ambient : Bool) : State → (arena ambient).History
  | .initial => (arena ambient).initHistory
  | .alice bit => aliceHistory ambient bit
  | .bob bit disclosed => bobHistory ambient bit disclosed
  | .done bit disclosed guess => guessHistory ambient bit disclosed guess

theorem historyOfState_state (ambient : Bool) (history : (arena ambient).History) :
    historyOfState ambient history.state = history := by
  have known : Classified ambient history := classified ambient history.trace
  rcases known with rfl | ⟨bit, rfl⟩ | ⟨bit, disclose, rfl⟩ | ⟨bit, disclose, guess, rfl⟩
  all_goals cases ambient <;> rfl

theorem state_injective (ambient : Bool) :
    Function.Injective (History.state (E := arena ambient)) :=
  Function.LeftInverse.injective (historyOfState_state ambient)

instance (ambient : Bool) : Finite (arena ambient).History :=
  Finite.of_injective _ (state_injective ambient)

instance (ambient : Bool) : Fintype (arena ambient).History := Fintype.ofFinite _

instance (ambient who : Bool) (site : (model ambient).InformationSite who) :
    Fintype ((model ambient).InformationHistory who site.1) := by
  classical
  infer_instance

theorem antichain (ambient : Bool) : (model ambient).DecisionInformationAntichain := by
  have length_at_decision (who : Bool) (history : (arena ambient).History)
      (active : (arena ambient).active history.state who) :
      history.trace.length = if who then 2 else 1 := by
    rw [history_length]
    cases state : history.state <;> cases ambient <;> cases who <;>
      simp_all [arena, actor, depth]
  intro who site first second joint legal target realized fuel path
  have firstLength := length_at_decision who first.1
    (InformationModel.InformationSite.active _ site first)
  have secondLength := length_at_decision who second.1
    (InformationModel.InformationSite.active _ site second)
  have increases := path.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at increases
  omega

def choose (ambient who value : Bool) : (model ambient).BehavioralPolicy who :=
  fun info => FinDist.pure ⟨if decisionInfo ambient who info then some value else none, by
    change (if decisionInfo ambient who info then some value else none).isSome =
      decisionInfo ambient who info
    cases decisionInfo ambient who info <;> rfl⟩

def choiceLaw {ambient : Bool} (profile : Profile (model ambient).behavioralSignature)
    (who : Bool) (info : Option (Option Bool)) : FinDist Bool :=
  (profile who info).map (fun choice => choice.val.getD false)

def kernel {ambient : Bool} (profile : Profile (model ambient).behavioralSignature) :
    State → FinDist State
  | .initial => (FinDist.uniformOfFintype (α := Bool)).map State.alice
  | .alice bit => (choiceLaw profile false (some (some bit))).map
      (fun disclose => .bob bit (ambient && disclose))
  | .bob bit disclosed => (choiceLaw profile true (some (if disclosed then some bit else none))).map
      (fun guess => .done bit disclosed guess)
  | .done bit disclosed guess => FinDist.pure (.done bit disclosed guess)

theorem chooser_kernel {ambient : Bool} (profile : Profile (model ambient).behavioralSignature)
    (history : (arena ambient).History) (running : ¬ (arena ambient).terminal history.state) :
    ((model ambient).singleMoverChooser (single ambient) profile history running).bind
      ((arena ambient).step history.state) = kernel profile history.state := by
  rcases history with ⟨state, trace⟩
  cases state with
  | initial => simp [arena, transition, kernel]
  | alice bit =>
      have marginal := (model ambient).singleMoverJoint_marginal (single ambient)
        profile ⟨_, trace⟩ running false
      rw [info_state] at marginal
      change ((model ambient).singleMoverJoint (single ambient) profile ⟨_, trace⟩ running).map
        (fun joint => joint.1 false) =
          (profile false (some (some bit))).map Subtype.val at marginal
      have mapped := congrArg (fun law => law.map
        (fun choice : Option Bool => State.bob bit (ambient && choice.getD false))) marginal
      simpa only [InformationModel.singleMoverChooser, arena, transition,
        kernel, choiceLaw, observation, ↓reduceIte, FinDist.map_comp,
        Function.comp_def, FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind,
        ite_true] using mapped
  | bob bit disclosed =>
      have marginal := (model ambient).singleMoverJoint_marginal (single ambient)
        profile ⟨_, trace⟩ running true
      rw [info_state] at marginal
      change ((model ambient).singleMoverJoint (single ambient) profile ⟨_, trace⟩ running).map
        (fun joint => joint.1 true) =
          (profile true (some (if disclosed then some bit else none))).map Subtype.val at marginal
      have mapped := congrArg (fun law => law.map
        (fun choice : Option Bool => State.done bit disclosed (choice.getD false))) marginal
      simpa only [InformationModel.singleMoverChooser, arena, transition,
        kernel, choiceLaw, observation, ↓reduceIte, FinDist.map_comp,
        Function.comp_def, FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind,
        ite_true] using mapped
  | done bit disclosed guess => exact (running trivial).elim

theorem run_states {ambient : Bool} (profile : Profile (model ambient).behavioralSignature)
    (fuel : Nat) (history : (arena ambient).History) :
    ((model ambient).runSingleMoverBehavioralFrom (single ambient) profile fuel history).map
      History.state = (fun law => law.bind (kernel profile))^[fuel]
        (FinDist.pure history.state) := by
  apply runRandomizedFor_map_state
  · intro state stopped
    cases state <;> try contradiction
    rfl
  · exact chooser_kernel profile

def resultLaw {ambient : Bool} (profile : Profile (model ambient).behavioralSignature)
    (bit disclosed : Bool) : FinDist State :=
  (choiceLaw profile true (some (if disclosed then some bit else none))).map
    (fun guess => .done bit disclosed guess)

theorem run_bob {ambient : Bool} (profile : Profile (model ambient).behavioralSignature)
    (bit disclose : Bool) :
    ((model ambient).runSingleMoverBehavioralFrom (single ambient) profile 3
      (bobHistory ambient bit disclose)).map History.state =
        resultLaw profile bit (ambient && disclose) := by
  rw [run_states]
  cases ambient <;>
    simp [Function.iterate_succ_apply', kernel, resultLaw, bobHistory, aliceHistory,
      History.extend, aliceJoint, FinDist.map_eq_bind]

theorem run_alice {ambient : Bool} (profile : Profile (model ambient).behavioralSignature)
    (bit : Bool) :
    ((model ambient).runSingleMoverBehavioralFrom (single ambient) profile 3
      (aliceHistory ambient bit)).map History.state =
        (choiceLaw profile false (some (some bit))).bind
          (fun disclose => resultLaw profile bit (ambient && disclose)) := by
  rw [run_states]
  simp [Function.iterate_succ_apply', kernel, resultLaw, aliceHistory,
    History.extend, FinDist.map_eq_bind, FinDist.bind_bind]

theorem run_initial {ambient : Bool} (profile : Profile (model ambient).behavioralSignature) :
    ((model ambient).runSingleMoverBehavioralFrom (single ambient) profile 3
      (arena ambient).initHistory).map History.state =
        (FinDist.uniformOfFintype (α := Bool)).bind fun bit =>
          (choiceLaw profile false (some (some bit))).bind fun disclose =>
            resultLaw profile bit (ambient && disclose) := by
  rw [run_states]
  simp [Function.iterate_succ_apply', kernel, resultLaw, initHistory,
    FinDist.map_eq_bind, FinDist.bind_bind]

def payoff (deposit : ℝ) : State → Bool → ℝ
  | .done bit disclosed guess, who =>
      (if guess = bit then 1 else 0) - (if !who && disclosed then deposit else 0)
  | _, _ => 0

def retained : State → Option (Bool × Bool)
  | .done bit _ guess => some (bit, guess)
  | _ => none

end GameTheoryExtensionsTests.AmbientEnforcement
