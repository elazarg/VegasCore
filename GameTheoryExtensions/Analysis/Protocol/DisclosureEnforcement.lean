/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion
import GameTheoryExtensions.Protocol.BehavioralContinuation
import GameTheoryExtensions.Protocol.StateKernel

/-! # Finite private-state decisions with optional authenticated disclosure

The source has a private finite state and one receiver decision. The extension
lets the informed sender disclose that state before the receiver acts. Both
players' utilities are arbitrary. The enforcement theorem charges the sender
only for disclosure. This protocol is a finite game class, not a native runtime.
-/

noncomputable section

namespace GameTheory.Protocol.DisclosureEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive State (Secret Decision : Type) where
  | initial
  | sender (secret : Secret)
  | receiver (secret : Secret) (disclosed : Bool)
  | done (secret : Secret) (disclosed : Bool) (decision : Decision)
  deriving DecidableEq, Fintype

variable {Secret Decision : Type} [Nonempty Decision]

@[reducible] def PlayerAction (Decision : Type) : Bool → Type
  | false => Bool
  | true => Decision

@[reducible] def fallback (who : Bool) : PlayerAction Decision who :=
  match who with
  | false => false
  | true => Classical.choice inferInstance

variable (prior : FinDist Secret)

def actor (ambient : Bool) : State Secret Decision → Option Bool
  | .sender _ => if ambient then some false else none
  | .receiver _ _ => some true
  | _ => none

def terminal : State Secret Decision → Prop
  | .done _ _ _ => True
  | _ => False

def transition (ambient : Bool) (state : State Secret Decision) (joint : (who : Bool) → Option
  (PlayerAction Decision who)) : FinDist (State Secret Decision) :=
  match state with
  | .initial => prior.map State.sender
  | .sender bit => FinDist.pure (.receiver bit (ambient && (joint false).getD false))
  | .receiver bit disclosed =>
      FinDist.pure (.done bit disclosed ((joint true).getD (fallback true)))
  | .done bit disclosed guess => FinDist.pure (.done bit disclosed guess)

@[reducible] def arena (ambient : Bool) : ExecutionProtocol Bool where
  State := State Secret Decision
  Action := PlayerAction Decision
  init := .initial
  active state who := actor ambient state = some who
  available _ _ := Set.univ
  terminal := terminal
  step state joint := transition prior ambient state joint.1
  progress state _ := by
    classical
    refine ⟨fun who => if actor ambient state = some who then some (fallback who) else none, ?_⟩
    intro who
    by_cases acts : actor ambient state = some who <;> simp [acts]

def depth : State Secret Decision → Nat
  | .initial => 0
  | .sender _ => 1
  | .receiver _ _ => 2
  | .done _ _ _ => 3

theorem history_length (ambient : Bool) : ∀ {state} (trace : (arena (Decision := Decision) prior
  ambient).Trace state),
    trace.length = depth state
  | _, .start => rfl
  | _, .extend (source := before) beforeTrace joint legal reached => by
      classical
      have earlier := history_length ambient beforeTrace
      cases before with
      | initial =>
          obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ reached
          simpa only [Trace.length, depth] using congrArg (· + 1) earlier
      | sender bit =>
          cases FinDist.mem_support_pure.mp reached
          simpa only [Trace.length, depth] using congrArg (· + 1) earlier
      | receiver bit disclosed =>
          cases FinDist.mem_support_pure.mp reached
          simpa only [Trace.length, depth] using congrArg (· + 1) earlier
      | done bit disclosed guess => exact (legal.1 trivial).elim

theorem bounded (ambient : Bool) : (arena (Decision := Decision) prior ambient).BoundedHorizon 3
  := by
  classical
  intro state trace enough
  rw [history_length prior ambient trace] at enough
  cases state <;> simp_all [depth, terminal]

theorem single (ambient : Bool) : ∀ state {first second},
    (arena (Decision := Decision) prior ambient).active state first → (arena (Decision :=
      Decision) prior ambient).active state second → first = second := by
  classical
  intro state first second left right
  exact Option.some.inj (left.symm.trans right)

def observation (who : Bool) : State Secret Decision → Option (Option Secret)
  | .sender bit => if who then none else some (some bit)
  | .receiver bit disclosed => if who then some (if disclosed then some bit else none) else none
  | _ => none

@[reducible] def signals (ambient : Bool) : InfoSignals (arena (Decision := Decision) prior
  ambient) where
  PublicSignal := Unit
  PrivateSignal _ := Option (Option Secret)
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := observation who event.target
  InfoState _ := Option (Option Secret)
  initInfo _ secret _ := secret
  pushInfo _ _ _ secret _ := secret

theorem info_state (ambient who : Bool) : ∀ {state} (trace : (arena (Decision := Decision) prior
  ambient).Trace state),
    (signals (Decision := Decision) prior ambient).infoOf who trace = observation who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def decisionInfo (ambient who : Bool) (info : Option (Option Secret)) : Bool :=
  (ambient || who) && info.isSome

@[reducible] def model (ambient : Bool) : InformationModel (arena (Decision := Decision) prior
  ambient) where
  toInfoSignals := signals (Decision := Decision) prior ambient
  menu who info := {choice | choice.isSome = decisionInfo ambient who info}
  menu_adequate who state trace choice := by
    classical
    rw [info_state]
    cases ambient <;> cases state <;> cases who <;> cases choice <;>
      simp [decisionInfo, observation, LegalOption, arena, actor]

def senderJoint (ambient disclose : Bool) : (who : Bool) → Option (PlayerAction Decision who) :=
  fun who => match who with | false => if ambient then some disclose else none | true => none

def receiverJoint (guess : Decision) : (who : Bool) → Option (PlayerAction Decision who) :=
  fun who =>
  match who with | false => none | true => some guess

theorem initial_legal (ambient : Bool) :
    (arena (Decision := Decision) prior ambient).Legal .initial (fun _ => none) := by
  classical
  exact ⟨id, fun _ => by simp [actor]⟩

theorem sender_legal (ambient : Bool) (bit : Secret) (disclose : Bool) :
    (arena (Decision := Decision) prior ambient).Legal (.sender bit) (senderJoint (Decision :=
      Decision) ambient disclose) := by
  classical
  constructor
  · simp [terminal]
  · intro who; cases ambient <;> cases who <;> simp [arena, actor, senderJoint]

theorem receiver_legal (ambient : Bool) (bit : Secret) (disclosed : Bool) (guess : Decision) :
    (arena (Decision := Decision) prior ambient).Legal
      (.receiver bit disclosed) (receiverJoint guess) := by
  classical
  constructor
  · simp [terminal]
  · intro who; cases who <;> simp [arena, actor, receiverJoint]

variable (full : ∀ secret, secret ∈ prior.support)

def senderHistory (ambient : Bool) (bit : Secret) : (arena (Decision := Decision) prior
  ambient).History :=
  (arena (Decision := Decision) prior ambient).initHistory.extend (target := .sender bit)
    (initial_legal prior ambient) (by
    change State.sender bit ∈ (prior.map State.sender).support
    rw [FinDist.support_map]
    exact ⟨bit, full bit, rfl⟩)

def receiverHistory (ambient : Bool) (bit : Secret) (disclose : Bool) :
    (arena (Decision := Decision)
  prior ambient).History :=
  (senderHistory prior full ambient bit).extend (sender_legal prior ambient bit disclose)
    (FinDist.mem_support_pure.mpr rfl)

def terminalHistory (ambient : Bool) (bit : Secret) (disclose : Bool) (guess : Decision) : (arena
  (Decision := Decision) prior ambient).History :=
  (receiverHistory prior full ambient bit disclose).extend
    (receiver_legal prior ambient bit (ambient && disclose) guess)
      (FinDist.mem_support_pure.mpr rfl)

theorem initial_joint (ambient : Bool) (joint : (who : Bool) → Option (PlayerAction Decision who))
    (legal : (arena (Decision := Decision) prior ambient).Legal .initial joint) : joint = fun _ =>
      none := by
  classical
  funext who
  exact LegalOption.eq_none_of_inactive (E := arena (Decision := Decision) prior ambient) (joint
    who)
    ((arena (Decision := Decision) prior ambient).legalOption_of_legal legal who) (by simp [actor])

theorem sender_joint (ambient : Bool) (bit : Secret) (joint : (who : Bool) → Option (PlayerAction
  Decision who))
    (legal : (arena (Decision := Decision) prior ambient).Legal (.sender bit) joint) :
    joint = senderJoint (Decision := Decision) ambient ((joint false).getD false) := by
  classical
  cases ambient
  · funext who
    have empty := LegalOption.eq_none_of_inactive
      (E := arena (Decision := Decision) prior false) (i := who) (state := .sender bit)
      (joint who) ((arena prior false).legalOption_of_legal legal who) (by simp [actor])
    cases who <;> exact empty
  · obtain ⟨ask, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena (Decision :=
    Decision) prior true) (i := false) (state := .sender bit) (joint false)
      ((arena (Decision := Decision) prior true).legalOption_of_legal legal false) rfl
    funext who
    cases who
    · simp [senderJoint, chosen]
    · exact LegalOption.eq_none_of_inactive (E := arena (Decision := Decision) prior true)
        (i := true) (state := .sender bit) (joint true)
        ((arena prior true).legalOption_of_legal legal true) (by simp [actor])

theorem receiver_joint (ambient : Bool) (bit : Secret) (disclosed : Bool) (joint : (who : Bool) →
  Option (PlayerAction Decision who))
    (legal : (arena (Decision := Decision) prior ambient).Legal (.receiver bit disclosed) joint) :
    joint = receiverJoint ((joint true).getD (fallback true)) := by
  classical
  obtain ⟨guess, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena (Decision :=
    Decision) prior ambient) (i := true) (state := .receiver bit disclosed) (joint true)
    ((arena (Decision := Decision) prior ambient).legalOption_of_legal legal true) rfl
  funext who
  cases who
  · exact LegalOption.eq_none_of_inactive (E := arena (Decision := Decision) prior ambient)
      (i := false) (state := .receiver bit disclosed) (joint false)
      ((arena prior ambient).legalOption_of_legal legal false) (by simp [actor])
  · simp [receiverJoint, chosen]

def Classified (ambient : Bool) (history : (arena (Decision := Decision) prior ambient).History) :
  Prop :=
  history = (arena (Decision := Decision) prior ambient).initHistory ∨ (∃ bit, history =
    senderHistory prior full ambient bit) ∨
    (∃ bit disclose, history = receiverHistory prior full ambient bit disclose) ∨
      ∃ bit disclose guess, history = terminalHistory prior full ambient bit disclose guess

theorem classified_step (ambient : Bool) (history : (arena (Decision := Decision) prior
  ambient).History)
    (known : Classified prior full ambient history) (joint : (who : Bool) → Option (PlayerAction
      Decision who))
    (legal : (arena (Decision := Decision) prior ambient).Legal history.state joint) (target :
      State Secret Decision)
    (reached : target ∈ ((arena (Decision := Decision) prior ambient).step history.state ⟨joint,
      legal⟩).support) :
    Classified prior full ambient (history.extend legal reached) := by
  classical
  rcases known with rfl | ⟨bit, rfl⟩ | ⟨bit, disclose, rfl⟩ | ⟨bit, disclose, guess, rfl⟩
  · have same := initial_joint prior ambient joint legal
    subst joint
    obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ reached
    exact Or.inr (Or.inl ⟨bit, rfl⟩)
  · have same := sender_joint prior ambient bit joint legal
    obtain ⟨disclose, same⟩ : ∃ disclose, joint = senderJoint (Decision := Decision) ambient
      disclose :=
      ⟨_, same⟩
    subst joint
    cases FinDist.mem_support_pure.mp reached
    exact Or.inr (Or.inr (Or.inl ⟨bit, disclose, rfl⟩))
  · have same := receiver_joint prior ambient bit (ambient && disclose) joint legal
    obtain ⟨guess, same⟩ : ∃ guess, joint = receiverJoint guess := ⟨_, same⟩
    subst joint
    cases FinDist.mem_support_pure.mp reached
    exact Or.inr (Or.inr (Or.inr ⟨bit, disclose, guess, rfl⟩))
  · exact (legal.1 trivial).elim

theorem classified (ambient : Bool) : ∀ {state} (trace : (arena (Decision := Decision) prior
  ambient).Trace state),
    Classified prior full ambient ⟨state, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend beforeTrace joint legal reached =>
      classified_step prior full ambient _ (classified ambient beforeTrace) joint legal
        _ reached

def historyOfState (ambient : Bool) : State Secret Decision → (arena (Decision := Decision) prior
  ambient).History
  | .initial => (arena (Decision := Decision) prior ambient).initHistory
  | .sender bit => senderHistory prior full ambient bit
  | .receiver bit disclosed => receiverHistory prior full ambient bit disclosed
  | .done bit disclosed guess => terminalHistory prior full ambient bit disclosed guess

theorem historyOfState_state (ambient : Bool) (history : (arena (Decision := Decision) prior
  ambient).History) :
    historyOfState prior full ambient history.state = history := by
  classical
  have known : Classified prior full ambient history := classified prior full ambient history.trace
  rcases known with rfl | ⟨bit, rfl⟩ | ⟨bit, disclose, rfl⟩ | ⟨bit, disclose, guess, rfl⟩
  all_goals cases ambient <;> rfl

include full in
theorem state_injective (ambient : Bool) :
    Function.Injective (History.state (E := arena (Decision := Decision) prior ambient)) :=
  Function.LeftInverse.injective (historyOfState_state prior full ambient)

theorem antichain (ambient : Bool) : (model (Decision := Decision) prior
  ambient).DecisionInformationAntichain := by
  classical
  have length_at_decision (who : Bool) (history : (arena (Decision := Decision) prior
    ambient).History)
      (active : (arena (Decision := Decision) prior ambient).active history.state who) :
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

variable {prior}

def choose (prior : FinDist Secret) (ambient who : Bool) (value : PlayerAction Decision who) :
  (model (Decision := Decision) prior ambient).BehavioralPolicy who :=
  fun info => FinDist.pure ⟨if decisionInfo ambient who info then some value else none, by
    change (if decisionInfo ambient who info then some value else none).isSome =
      decisionInfo ambient who info
    cases decisionInfo ambient who info <;> rfl⟩

def choiceLaw {ambient : Bool} (profile : Profile (model (Decision := Decision) prior
  ambient).behavioralSignature)
    (who : Bool) (info : Option (Option Secret)) : FinDist (PlayerAction Decision who) :=
  (profile who info).map (fun choice => choice.val.getD (fallback who))

def kernel {ambient : Bool} (profile : Profile (model (Decision := Decision) prior
  ambient).behavioralSignature) :
    State Secret Decision → FinDist (State Secret Decision)
  | .initial => prior.map State.sender
  | .sender bit => (choiceLaw profile false (some (some bit))).map
      (fun disclose => .receiver bit (ambient && disclose))
  | .receiver bit disclosed =>
      (choiceLaw profile true (some (if disclosed then some bit else none))).map
      (fun guess => .done bit disclosed guess)
  | .done bit disclosed guess => FinDist.pure (.done bit disclosed guess)

theorem chooser_kernel {ambient : Bool} (profile : Profile (model (Decision := Decision) prior
  ambient).behavioralSignature)
    (history : (arena (Decision := Decision) prior ambient).History) (running : ¬ (arena (Decision
      := Decision) prior ambient).terminal history.state) :
    ((model (Decision := Decision) prior ambient).singleMoverChooser (single prior ambient)
      profile history running).bind
      ((arena (Decision := Decision) prior ambient).step history.state) = kernel profile
        history.state := by
  classical
  rcases history with ⟨state, trace⟩
  cases state with
  | initial => simp [arena, transition, kernel]
  | sender bit =>
      have marginal := (model (Decision := Decision) prior ambient).singleMoverJoint_marginal
        (single prior ambient)
        profile ⟨_, trace⟩ running false
      rw [info_state] at marginal
      change ((model (Decision := Decision) prior ambient).singleMoverJoint (single prior ambient)
        profile ⟨_, trace⟩ running).map
        (fun joint => joint.1 false) =
          (profile false (some (some bit))).map Subtype.val at marginal
      have mapped := congrArg (fun law => law.map
        (fun choice : Option Bool =>
          State.receiver (Decision := Decision) bit (ambient && choice.getD false))) marginal
      simpa only [InformationModel.singleMoverChooser, arena, transition,
        kernel, choiceLaw, observation, ↓reduceIte, FinDist.map_comp,
        Function.comp_def, FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind,
        ite_true] using mapped
  | receiver bit disclosed =>
      have marginal := (model (Decision := Decision) prior ambient).singleMoverJoint_marginal
        (single prior ambient)
        profile ⟨_, trace⟩ running true
      rw [info_state] at marginal
      change ((model (Decision := Decision) prior ambient).singleMoverJoint (single prior ambient)
        profile ⟨_, trace⟩ running).map
        (fun joint => joint.1 true) =
          (profile true (some (if disclosed then some bit else none))).map Subtype.val at marginal
      have mapped := congrArg (fun law => law.map
        (fun choice : Option Decision => State.done bit disclosed (choice.getD (fallback true))))
          marginal
      simpa only [InformationModel.singleMoverChooser, arena, transition,
        kernel, choiceLaw, observation, ↓reduceIte, FinDist.map_comp,
        Function.comp_def, FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind,
        ite_true] using mapped
  | done bit disclosed guess => exact (running trivial).elim

theorem run_states {ambient : Bool} (profile : Profile (model (Decision := Decision) prior
  ambient).behavioralSignature)
    (fuel : Nat) (history : (arena (Decision := Decision) prior ambient).History) :
    ((model (Decision := Decision) prior ambient).runSingleMoverBehavioralFrom (single prior
      ambient) profile fuel history).map
      History.state = (fun law => law.bind (kernel profile))^[fuel]
        (FinDist.pure history.state) := by
  classical
  apply runRandomizedFor_map_state
  · intro state stopped
    cases state <;> try contradiction
    rfl
  · exact chooser_kernel profile

def resultLaw {ambient : Bool} (profile : Profile (model (Decision := Decision) prior
  ambient).behavioralSignature)
    (bit : Secret) (disclosed : Bool) : FinDist (State Secret Decision) :=
  (choiceLaw profile true (some (if disclosed then some bit else none))).map
    (fun guess => .done bit disclosed guess)

theorem run_receiver {ambient : Bool} (profile : Profile (model (Decision := Decision) prior
  ambient).behavioralSignature)
    (bit : Secret) (disclose : Bool) :
    ((model (Decision := Decision) prior ambient).runSingleMoverBehavioralFrom (single prior
      ambient) profile 3
      (receiverHistory prior full ambient bit disclose)).map History.state =
        resultLaw profile bit (ambient && disclose) := by
  classical
  rw [run_states]
  cases ambient <;>
    simp [Function.iterate_succ_apply', kernel, resultLaw, receiverHistory, senderHistory,
      History.extend, senderJoint, FinDist.map_eq_bind]

theorem run_sender {ambient : Bool} (profile : Profile (model (Decision := Decision) prior
  ambient).behavioralSignature)
    (bit : Secret) :
    ((model (Decision := Decision) prior ambient).runSingleMoverBehavioralFrom (single prior
      ambient) profile 3
      (senderHistory prior full ambient bit)).map History.state =
        (choiceLaw profile false (some (some bit))).bind
          (fun disclose => resultLaw profile bit (ambient && disclose)) := by
  classical
  rw [run_states]
  simp [Function.iterate_succ_apply', kernel, resultLaw, senderHistory,
    History.extend, FinDist.map_eq_bind, FinDist.bind_bind]

theorem run_initial {ambient : Bool} (profile : Profile (model (Decision := Decision) prior
  ambient).behavioralSignature) :
    ((model (Decision := Decision) prior ambient).runSingleMoverBehavioralFrom (single prior
      ambient) profile 3
      (arena (Decision := Decision) prior ambient).initHistory).map History.state =
        prior.bind fun bit =>
          (choiceLaw profile false (some (some bit))).bind fun disclose =>
            resultLaw profile bit (ambient && disclose) := by
  classical
  rw [run_states]
  simp [Function.iterate_succ_apply', kernel, resultLaw, initHistory,
    FinDist.map_eq_bind, FinDist.bind_bind]

def payoff (sender receiver : Secret → Decision → ℝ) (charge : Secret → ℝ) :
    State Secret Decision → Bool → ℝ
  | .done secret disclosed action, false => sender secret action - if disclosed then charge secret
    else 0
  | .done secret _ action, true => receiver secret action
  | _, _ => 0

def retained : State Secret Decision → Option (Secret × Decision)
  | .done bit _ guess => some (bit, guess)
  | _ => none

instance [Fintype Decision] (who : Bool) : Fintype (PlayerAction Decision who) := by
  cases who <;> infer_instance

instance (who : Bool) : Nonempty (PlayerAction Decision who) := ⟨fallback who⟩

/-- A finite fully mixed reference; the sender trembles equally at all private states. -/
def reference [Fintype Decision] (prior : FinDist Secret) (ambient : Bool) :
    (model (Decision := Decision) prior ambient).BehavioralAssessment :=
  .ofStrategy fun who info => (FinDist.uniformOfFintype (α := PlayerAction Decision who)).bind
    (fun value => choose prior ambient who value info)

theorem reference_full [Fintype Decision] (prior : FinDist Secret) (ambient : Bool) :
    (reference (Decision := Decision) prior ambient).IsFullyMixed := by
  classical
  intro who site choice
  change choice ∈ ((FinDist.uniformOfFintype (α := PlayerAction Decision who)).bind
    (fun value => choose prior ambient who value site.1)).support
  simp only [FinDist.support_bind, Set.mem_iUnion]
  refine ⟨choice.val.getD (fallback who), FinDist.mem_support_uniformOfFintype _, ?_⟩
  rw [choose, FinDist.mem_support_pure]
  apply Subtype.ext
  have legal := choice.property
  change choice.val.isSome = decisionInfo ambient who site.1 at legal
  cases value : choice.val <;> simp_all

instance [Finite Decision] (prior : FinDist Secret) (ambient : Bool) :
    Finite (arena (Decision := Decision) prior ambient).History := by
  classical
  let := Fintype.ofFinite Decision
  exact (reference_full (Decision := Decision) prior ambient).finite_history
    (bounded prior ambient)

instance [Finite Decision] (prior : FinDist Secret) (ambient : Bool) :
    Fintype (arena (Decision := Decision) prior ambient).History := Fintype.ofFinite _

instance [Finite Decision] (prior : FinDist Secret) (ambient who : Bool)
    (site : (model (Decision := Decision) prior ambient).InformationSite who) :
    Fintype ((model (Decision := Decision) prior ambient).InformationHistory who site.1) := by
  classical
  infer_instance

end GameTheory.Protocol.DisclosureEnforcement
