/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.Communication
import GameTheoryExtensions.Protocol.ObservationRecall

/-! # A bounded communication extension of an information game

A fixed public roster provides optional communication opportunities before
each underlying transition. A communication changes only the transcript;
an underlying transition uses exactly the original game kernel. The adapter
may also emit evidence when an underlying action occurs. Such emissions are
observations and do not change the original game's result type.

This is a synchronous semantic service, not a model of arbitrary asynchronous
communication. Its roster, delivery rule, and observable phase boundaries are
explicit assumptions. A runtime must implement the chosen service before an
equilibrium theorem can be applied to it.
-/

noncomputable section

namespace Interaction

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open Communication

/-- Evidence available from a player's game observation, and observations
emitted by game transitions. All truth and persistence obligations are explicit. -/
structure CommunicationInterface {Player : Type} {E : ExecutionProtocol Player}
    (M : InformationModel E) where
  Claim : Type
  Evidence : Type
  possesses : (who : Player) → M.InfoState who → Evidence → Prop
  valid : E.History → Evidence → Prop
  sound : ∀ who history fact, possesses who (M.infoOf who history.trace) fact → valid history fact
  persists : ∀ (history : E.History) joint (legal : E.Legal history.state joint)
    target (realized : target ∈ (E.step history.state ⟨joint, legal⟩).support) fact,
    valid history fact → valid (history.extend legal realized) fact
  emissions : StepEvent E → List (Message Player Claim Evidence)
  emissions_sound : ∀ (history : E.History) joint (legal : E.Legal history.state joint)
    target (realized : target ∈ (E.step history.state ⟨joint, legal⟩).support)
    message, message ∈ emissions ⟨history.state, joint, legal, target, realized⟩ →
    ∀ fact, message.content = .evidence fact → valid (history.extend legal realized) fact

namespace CommunicationInterface

variable {Player : Type} {E : ExecutionProtocol Player} {M : InformationModel E}
  (channel : CommunicationInterface M)

def evidenceModel : EvidenceModel Player E.History where
  Evidence := channel.Evidence
  View := M.InfoState
  observe who history := M.infoOf who history.trace
  possesses := channel.possesses
  valid := channel.valid
  sound := channel.sound

abbrev Outgoing := Audience Player × Content channel.Claim channel.Evidence
abbrev Action (who : Player) := E.Action who ⊕ Option channel.Outgoing

structure State where
  history : E.History
  remaining : List Player
  transcript : Transcript Player channel.Claim channel.Evidence

/-- The phase counter counts underlying game transitions, not blockchain time. -/
structure View (who : Player) where
  game : M.InfoState who
  phase : Nat
  remaining : List Player
  transcript : Transcript Player channel.Claim channel.Evidence

def observe (state : channel.State) (who : Player) : channel.View who where
  game := M.infoOf who state.history.trace
  phase := state.history.trace.length
  remaining := state.remaining
  transcript := state.transcript.observe who

def allowed (who : Player) (view : channel.View who) (outgoing : channel.Outgoing) : Prop :=
  match outgoing.2 with
  | .claim _ => True
  | .evidence fact => channel.possesses who view.game fact ∨
      ∃ message ∈ view.transcript, message.content = .evidence fact

def menu (who : Player) (view : channel.View who) : Set (Option (channel.Action who)) := {choice |
  match view.remaining with
  | [] => match choice with
    | none => none ∈ M.menu who view.game
    | some (.inl action) => some action ∈ M.menu who view.game
    | some (.inr _) => False
  | actor :: _ => match choice with
    | none => actor ≠ who
    | some (.inl _) => False
    | some (.inr outgoing) => actor = who ∧ outgoing.elim True (channel.allowed who view) }

def active (state : channel.State) (who : Player) : Prop :=
  match state.remaining with
  | [] => E.active state.history.state who
  | actor :: _ => actor = who

def available (state : channel.State) (who : Player) : Set (channel.Action who) := {action |
  match state.remaining, action with
  | [], .inl action => action ∈ E.available state.history.state who
  | _ :: _, .inr outgoing => outgoing.elim True (channel.allowed who (channel.observe state who))
  | _, _ => False }

def gameJoint (joint : ∀ who, Option (channel.Action who)) : ∀ who, Option (E.Action who) :=
  fun who => (joint who).bind fun action => action.elim some (fun _ => none)

theorem gameJoint_legal (state : channel.State) (joint : ∀ who, Option (channel.Action who))
    (empty : state.remaining = [])
    (running : ¬ E.terminal state.history.state)
    (legal : IsLegalJoint (channel.active state) (channel.available state) joint) :
    E.Legal state.history.state (channel.gameJoint joint) := by
  refine ⟨running, fun who => ?_⟩
  have own := legal who
  cases chosen : joint who with
  | none => simpa [gameJoint, chosen, active, empty] using own
  | some action =>
      cases action with
      | inl action => simpa [gameJoint, chosen, active, available, empty] using own
      | inr outgoing => simp [chosen, available, empty] at own

def communicate (state : channel.State) (actor : Player) (rest : List Player)
    (outgoing : Option channel.Outgoing) : channel.State :=
  { state with remaining := rest
               transcript := state.transcript ++ (outgoing.toList.map fun message =>
                 ⟨actor, message.1, message.2⟩) }

/-- A communication has no effect on the underlying history or any readout of it. -/
@[simp] theorem communicate_history (state : channel.State) (actor : Player)
    (rest : List Player) (outgoing : Option channel.Outgoing) :
    (channel.communicate state actor rest outgoing).history = state.history := rfl

def advance (roster : List Player) (state : channel.State)
    (joint : ∀ who, Option (E.Action who)) (legal : E.Legal state.history.state joint)
    (target : E.State) (realized : target ∈ (E.step state.history.state ⟨joint, legal⟩).support) :
    channel.State where
  history := state.history.extend legal realized
  remaining := roster
  transcript := state.transcript ++
    channel.emissions ⟨state.history.state, joint, legal, target, realized⟩

def gameTransition (roster : List Player) (state : channel.State)
    (joint : {joint : ∀ who, Option (E.Action who) // E.Legal state.history.state joint}) :
    FinDist channel.State :=
  (E.step state.history.state joint).bindOnSupport fun target realized =>
    FinDist.pure (channel.advance roster state joint.1 joint.2 target realized)

def transition (roster : List Player) (state : channel.State)
    (joint : ∀ who, Option (channel.Action who))
    (running : ¬ E.terminal state.history.state)
    (legal : IsLegalJoint (channel.active state) (channel.available state) joint) :
    FinDist channel.State :=
  match empty : state.remaining with
  | [] =>
      let admitted := channel.gameJoint_legal state joint empty running legal
      channel.gameTransition roster state ⟨channel.gameJoint joint, admitted⟩
  | actor :: rest => FinDist.pure (channel.communicate state actor rest
      ((joint actor).bind fun action => action.elim (fun _ => none) id))

open Classical in
def protocol (roster : List Player) : ExecutionProtocol Player where
  State := channel.State
  Action := channel.Action
  init := ⟨E.initHistory, roster, []⟩
  active := channel.active
  available := channel.available
  terminal state := E.terminal state.history.state
  step state joint := channel.transition roster state joint.1 joint.2.1 joint.2.2
  progress state running := by
    cases pending : state.remaining with
    | nil =>
        obtain ⟨joint, legal⟩ := E.progress state.history.state running
        refine ⟨fun who => (joint who).map Sum.inl, fun who => ?_⟩
        have own := legal who
        cases chosen : joint who <;> simpa [chosen, active, available, pending] using own
    | cons actor rest =>
        refine ⟨fun who => if actor = who then some (.inr none) else none, fun who => ?_⟩
        by_cases same : actor = who <;> simp [same, active, available, pending]

def currentSignals (roster : List Player) : InfoSignals (channel.protocol roster) where
  PublicSignal := Unit
  PrivateSignal := channel.View
  initialPublic := ()
  initialPrivate who := channel.observe ⟨E.initHistory, roster, []⟩ who
  publicSignal _ := ()
  privateSignal who event := channel.observe event.target who
  InfoState who := channel.View who
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

def signals (roster : List Player) : InfoSignals (channel.protocol roster) :=
  (channel.currentSignals roster).withObservationRecall

theorem info (roster : List Player) (who : Player) :
    ∀ {state} (trace : (channel.protocol roster).Trace state),
      ((channel.signals roster).infoOf who trace).current = channel.observe state who := by
  intro state trace
  change ((channel.currentSignals roster).withObservationRecall.infoOf who trace).current = _
  rw [InfoSignals.withObservationRecall_current]
  cases trace <;> rfl

def informationModel (roster : List Player) : InformationModel (channel.protocol roster) where
  toInfoSignals := channel.signals roster
  menu who view := channel.menu who view.current
  menu_adequate := by
    intro who state trace choice
    change choice ∈ channel.menu who
      (((channel.signals roster).infoOf who trace).current) ↔ _
    rw [channel.info]
    cases pending : state.remaining with
    | nil =>
        have adequate := M.menu_adequate who state.history.trace
        cases choice with
        | none => simpa [menu, observe, pending, LegalOption, protocol, active] using adequate none
        | some action =>
            cases action with
            | inl action =>
                simpa [menu, observe, pending, LegalOption, protocol, active, available] using
                  adequate (some action)
            | inr outgoing =>
                simp [menu, observe, pending, LegalOption, protocol, active, available]
    | cons actor rest =>
        cases choice with
        | none => simp [menu, observe, pending, LegalOption, protocol, active]
        | some action =>
            cases action <;> simp [menu, observe, pending, LegalOption, protocol, active, available]

theorem perfectRecall (roster : List Player) :
    (channel.informationModel roster).PerfectRecall :=
  (channel.currentSignals roster).withObservationRecall_perfectRecall

theorem information_current (roster : List Player) (who : Player)
    {state : channel.State} (trace : (channel.protocol roster).Trace state) :
    ((channel.informationModel roster).infoOf who trace).current = channel.observe state who :=
  channel.info roster who trace

end CommunicationInterface
end Interaction
