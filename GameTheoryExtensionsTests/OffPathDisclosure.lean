/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.BehavioralContinuation
import GameTheoryExtensions.Protocol.StateKernel

/-! # A private type disclosed only after an earlier deviation

Chance gives Alice a bit. Alice can stop, or ask Bob to guess it. The source
keeps the bit private; the target reveals it when Bob is asked. Alice's payoff
is zero. Prescribed Alice stops, so Bob's later incentives do not affect play
from initialization. The two protocols share all actions and transitions.
Only Bob's observation differs. This is an abstract information experiment,
not a claim that the reactive runtime implements this disclosure channel.
-/

noncomputable section

namespace GameTheoryExtensionsTests.OffPathDisclosure

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

/-- Players are `false` (Alice) and `true` (Bob). -/
inductive State where
  | initial
  | alice (bit : Bool)
  | bob (bit : Bool)
  | done (bit : Bool) (guess : Option Bool)
  deriving DecidableEq

def actor : State → Option Bool
  | .alice _ => some false
  | .bob _ => some true
  | _ => none

def terminal : State → Prop
  | .done _ _ => True
  | _ => False

def transition (state : State) (joint : Bool → Option Bool) : FinDist State :=
  match state with
  | .initial => (FinDist.uniformOfFintype (α := Bool)).map State.alice
  | .alice bit => FinDist.pure (if (joint false).getD false then .bob bit else .done bit none)
  | .bob bit => FinDist.pure (.done bit (some ((joint true).getD false)))
  | .done bit guess => FinDist.pure (.done bit guess)

@[reducible] def arena : ExecutionProtocol Bool where
  State := State
  Action _ := Bool
  init := .initial
  active state who := actor state = some who
  available _ _ := Set.univ
  terminal := terminal
  step state joint := transition state joint.1
  progress state running := by
    refine ⟨fun who => if actor state = some who then some false else none, ?_⟩
    intro who
    by_cases active : actor state = some who <;> simp [active]

def depth : State → Nat
  | .initial => 0
  | .alice _ => 1
  | .bob _ => 2
  | .done _ none => 2
  | .done _ (some _) => 3

theorem history_length : ∀ {state} (trace : arena.Trace state), trace.length = depth state
  | _, .start => rfl
  | _, .extend (source := before) prior joint legal reached => by
      have earlier := history_length prior
      cases before with
      | initial =>
          obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ reached
          simpa only [Trace.length, depth] using congrArg (· + 1) earlier
      | alice bit =>
          cases FinDist.mem_support_pure.mp reached
          change prior.length + 1 = depth (if (joint false).getD false then _ else _)
          split <;> simpa only [depth] using congrArg (· + 1) earlier
      | bob bit =>
          cases FinDist.mem_support_pure.mp reached
          simpa only [Trace.length, depth] using congrArg (· + 1) earlier
      | done bit guess => exact (legal.1 trivial).elim

theorem bounded : arena.BoundedHorizon 3 := by
  intro state trace enough
  rw [history_length trace] at enough
  cases state <;> simp_all [depth, terminal]

theorem single : ∀ state {first second},
    arena.active state first → arena.active state second → first = second := by
  intro state first second left right
  exact Option.some.inj (left.symm.trans right)

def observation (disclose : Bool) (who : Bool) : State → Option Bool
  | .alice bit => if who = false then some bit else none
  | .bob bit => if who = true then some (if disclose then bit else false) else none
  | _ => none

@[reducible] def signals (disclose : Bool) : InfoSignals arena where
  PublicSignal := Unit
  PrivateSignal _ := Option Bool
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := observation disclose who event.target
  InfoState _ := Option Bool
  initInfo _ secret _ := secret
  pushInfo _ _ _ secret _ := secret

theorem info_state (disclose who : Bool) : ∀ {state} (trace : arena.Trace state),
    (signals disclose).infoOf who trace = observation disclose who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def model (disclose : Bool) : InformationModel arena where
  toInfoSignals := signals disclose
  menu _ info := {choice | choice.isSome = info.isSome}
  menu_adequate who state trace choice := by
    rw [info_state]
    cases state <;> cases who <;> cases choice <;> simp [observation, LegalOption, arena, actor]

def aliceJoint (ask : Bool) : Bool → Option Bool := fun who => if who then none else some ask
def bobJoint (guess : Bool) : Bool → Option Bool := fun who => if who then some guess else none

theorem initial_legal : arena.Legal .initial (fun _ => none) := by
  exact ⟨id, fun _ => by simp [actor]⟩

theorem alice_legal (bit ask : Bool) : arena.Legal (.alice bit) (aliceJoint ask) := by
  constructor
  · simp [terminal]
  · intro who; cases who <;> simp [arena, actor, aliceJoint]

theorem bob_legal (bit guess : Bool) : arena.Legal (.bob bit) (bobJoint guess) := by
  constructor
  · simp [terminal]
  · intro who; cases who <;> simp [arena, actor, bobJoint]

def aliceHistory (bit : Bool) : arena.History :=
  arena.initHistory.extend (target := .alice bit) initial_legal (by
    change State.alice bit ∈ ((FinDist.uniformOfFintype (α := Bool)).map State.alice).support
    rw [FinDist.support_map]
    exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩)

def bobHistory (bit : Bool) : arena.History :=
  (aliceHistory bit).extend (alice_legal bit true) (FinDist.mem_support_pure.mpr rfl)

def stopHistory (bit : Bool) : arena.History :=
  (aliceHistory bit).extend (alice_legal bit false) (FinDist.mem_support_pure.mpr rfl)

def guessHistory (bit guess : Bool) : arena.History :=
  (bobHistory bit).extend (bob_legal bit guess) (FinDist.mem_support_pure.mpr rfl)

theorem initial_joint (joint : Bool → Option Bool) (legal : arena.Legal .initial joint) :
    joint = fun _ => none := by
  funext who
  exact LegalOption.eq_none_of_inactive (E := arena) (joint who)
    (arena.legalOption_of_legal legal who) (by simp [actor])

theorem alice_joint (bit : Bool) (joint : Bool → Option Bool)
    (legal : arena.Legal (.alice bit) joint) : joint = aliceJoint ((joint false).getD false) := by
  obtain ⟨ask, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena) (joint false)
    (arena.legalOption_of_legal legal false) rfl
  funext who
  cases who
  · simp [aliceJoint, chosen]
  · exact LegalOption.eq_none_of_inactive (E := arena) (joint true)
      (arena.legalOption_of_legal legal true) (by simp [actor])

theorem bob_joint (bit : Bool) (joint : Bool → Option Bool)
    (legal : arena.Legal (.bob bit) joint) : joint = bobJoint ((joint true).getD false) := by
  obtain ⟨guess, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena) (joint true)
    (arena.legalOption_of_legal legal true) rfl
  funext who
  cases who
  · exact LegalOption.eq_none_of_inactive (E := arena) (joint false)
      (arena.legalOption_of_legal legal false) (by simp [actor])
  · simp [bobJoint, chosen]

def Classified (history : arena.History) : Prop :=
  history = arena.initHistory ∨ (∃ bit, history = aliceHistory bit) ∨
    (∃ bit, history = bobHistory bit) ∨ (∃ bit, history = stopHistory bit) ∨
      ∃ bit guess, history = guessHistory bit guess

theorem classified_step (history : arena.History) (known : Classified history)
    (joint : Bool → Option Bool) (legal : arena.Legal history.state joint)
    (target : State) (reached : target ∈ (arena.step history.state ⟨joint, legal⟩).support) :
    Classified (history.extend legal reached) := by
  rcases known with rfl | ⟨bit, rfl⟩ | ⟨bit, rfl⟩ | ⟨bit, rfl⟩ | ⟨bit, guess, rfl⟩
  · have same := initial_joint joint legal
    subst joint
    obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ reached
    exact Or.inr (Or.inl ⟨bit, rfl⟩)
  · obtain ⟨ask, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena) (joint false)
      (arena.legalOption_of_legal legal false) rfl
    have same : joint = aliceJoint ask := by
      simpa only [chosen, Option.getD_some] using alice_joint bit joint legal
    subst joint
    cases FinDist.mem_support_pure.mp reached
    cases ask
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨bit, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨bit, rfl⟩))
  · obtain ⟨guess, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena) (joint true)
      (arena.legalOption_of_legal legal true) rfl
    have same : joint = bobJoint guess := by
      simpa only [chosen, Option.getD_some] using bob_joint bit joint legal
    subst joint
    cases FinDist.mem_support_pure.mp reached
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨bit, guess, rfl⟩)))
  · exact (legal.1 trivial).elim
  · exact (legal.1 trivial).elim

theorem classified : ∀ {state} (trace : arena.Trace state), Classified ⟨state, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend prior joint legal reached =>
      classified_step _ (classified prior) joint legal _ reached

theorem reached_terminal_eq {fuel : Nat} {start finish : arena.History}
    (path : arena.ReachesWithin fuel start finish) (stopped : arena.terminal start.state) :
    finish = start := by
  cases path with
  | refl => rfl
  | step _ legal _ _ => exact (legal.1 stopped).elim

theorem alice_not_proper (bit : Bool) : ¬ (model false).IsSubgameRoot (aliceHistory bit) := by
  intro proper
  have reached := proper true (bobHistory bit) (bobHistory (!bit))
    (HistoryReaches.step arena (alice_legal bit true) (FinDist.mem_support_pure.mpr rfl)
      (HistoryReaches.refl _ _)) (by exact id) rfl (by exact id) rfl rfl
  obtain ⟨fuel, path⟩ := reached
  cases path with
  | @step _ _ _ joint legal target selected suffix =>
      obtain ⟨ask, chosen⟩ := LegalOption.exists_eq_some_of_active (E := arena) (joint false)
        (arena.legalOption_of_legal legal false) rfl
      have equal : joint = aliceJoint ask := by
        simpa only [chosen, Option.getD_some] using alice_joint bit joint legal
      subst joint
      cases ask
      · cases FinDist.mem_support_pure.mp selected
        have impossible := reached_terminal_eq suffix (by trivial)
        have states := congrArg ExecutionProtocol.History.state impossible
        cases states
      · cases FinDist.mem_support_pure.mp selected
        have equal := suffix.eq_of_trace_length_eq rfl
        have states := congrArg ExecutionProtocol.History.state equal
        cases bit <;> cases states

theorem bob_not_proper (bit : Bool) : ¬ (model false).IsSubgameRoot (bobHistory bit) := by
  intro proper
  have reached := proper true (bobHistory bit) (bobHistory (!bit))
    (HistoryReaches.refl _ _) (by exact id) rfl (by exact id) rfl rfl
  obtain ⟨fuel, path⟩ := reached
  have equal := path.eq_of_trace_length_eq rfl
  have states := congrArg ExecutionProtocol.History.state equal
  cases bit <;> cases states

theorem source_proper_initial_or_terminal (history : arena.History)
    (proper : (model false).IsSubgameRoot history) :
    history = arena.initHistory ∨ arena.terminal history.state := by
  have known : Classified history := classified history.trace
  rcases known with rfl | ⟨bit, rfl⟩ | ⟨bit, rfl⟩ |
    ⟨bit, rfl⟩ | ⟨bit, guess, rfl⟩
  · exact Or.inl rfl
  · exact (alice_not_proper bit proper).elim
  · exact (bob_not_proper bit proper).elim
  · exact Or.inr trivial
  · exact Or.inr trivial

theorem bob_proper (bit : Bool) : (model true).IsSubgameRoot (bobHistory bit) := by
  intro who inside outside reached running active _ outsideActive same
  obtain ⟨fuel, path⟩ := reached
  have insideEq : inside = bobHistory bit := by
    cases path with
    | refl => rfl
    | @step _ _ _ joint legal target selected suffix =>
        cases FinDist.mem_support_pure.mp selected
        have same := reached_terminal_eq suffix (by trivial)
        cases same
        exact (running trivial).elim
  subst inside
  have player : who = true := (Option.some.inj active).symm
  subst who
  have known : Classified outside := classified outside.trace
  rcases known with rfl | ⟨other, rfl⟩ | ⟨other, rfl⟩ |
    ⟨other, rfl⟩ | ⟨other, guess, rfl⟩
  all_goals try cases outsideActive
  have equal : bit = other := Option.some.inj same
  subst other
  exact HistoryReaches.refl _ _

end GameTheoryExtensionsTests.OffPathDisclosure
