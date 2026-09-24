/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommunicationProtocol

/-! # Legal communication and unchanged game transitions

These constructors build actual histories of the extension. They witness
optional disclosure independently of game actions. With an empty roster,
every legal base history acquires exactly the evidence emitted by its actions.
-/

noncomputable section

namespace Interaction.CommunicationInterface

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} {E : ExecutionProtocol Player} {M : InformationModel E}
  (channel : CommunicationInterface M)

open Classical in
def communicationJoint (actor : Player) (outgoing : Option channel.Outgoing) :
    ∀ who, Option (channel.Action who) :=
  fun who => if who = actor then some (.inr outgoing) else none

theorem communication_legal (roster : List Player) (state : channel.State)
    (actor : Player) (rest : List Player) (pending : state.remaining = actor :: rest)
    (running : ¬ E.terminal state.history.state) (outgoing : Option channel.Outgoing)
    (allowed : outgoing.elim True (channel.allowed actor (channel.observe state actor))) :
    (channel.protocol roster).Legal state (channel.communicationJoint actor outgoing) := by
  classical
  refine ⟨running, fun who => ?_⟩
  by_cases same : who = actor
  · subst who
    simpa [communicationJoint, protocol, active, available, pending] using allowed
  · simp [communicationJoint, same, protocol, active, pending, Ne.symm same]

theorem communication_step (roster : List Player) (state : channel.State)
    (actor : Player) (rest : List Player) (pending : state.remaining = actor :: rest)
    (running : ¬ E.terminal state.history.state) (outgoing : Option channel.Outgoing)
    (allowed : outgoing.elim True (channel.allowed actor (channel.observe state actor))) :
    (channel.protocol roster).step state
      ⟨_, channel.communication_legal roster state actor rest pending running outgoing allowed⟩ =
      FinDist.pure (channel.communicate state actor rest outgoing) := by
  dsimp only [protocol]
  unfold transition
  split
  · rename_i empty
    rw [pending] at empty
    cases empty
  · rename_i who tail same
    have equal := same.symm.trans pending
    obtain ⟨rfl, rfl⟩ := List.cons.inj equal
    simp [communicationJoint]

def communicateHistory (roster : List Player) (history : (channel.protocol roster).History)
    (actor : Player) (rest : List Player) (pending : history.state.remaining = actor :: rest)
    (running : ¬ E.terminal history.state.history.state) (outgoing : Option channel.Outgoing)
    (allowed : outgoing.elim True (channel.allowed actor (channel.observe history.state actor))) :
    (channel.protocol roster).History :=
  history.extend (channel.communication_legal roster history.state actor rest
    pending running outgoing allowed)
    (target := channel.communicate history.state actor rest outgoing)
    (by
      rw [channel.communication_step roster history.state actor rest pending
        running outgoing allowed]
      exact FinDist.mem_support_pure.mpr rfl)

def liftedJoint (joint : ∀ who, Option (E.Action who)) : ∀ who, Option (channel.Action who) :=
  fun who => (joint who).map Sum.inl

@[simp] theorem gameJoint_liftedJoint (joint : ∀ who, Option (E.Action who)) :
    channel.gameJoint (channel.liftedJoint joint) = joint := by
  funext who
  cases chosen : joint who <;> simp [gameJoint, liftedJoint, chosen]

theorem game_legal (roster : List Player) (state : channel.State)
    (empty : state.remaining = []) (joint : ∀ who, Option (E.Action who))
    (legal : E.Legal state.history.state joint) :
    (channel.protocol roster).Legal state (channel.liftedJoint joint) := by
  refine ⟨legal.1, fun who => ?_⟩
  have own := legal.2 who
  cases chosen : joint who <;>
    simpa [liftedJoint, chosen, protocol, active, available, empty] using own

theorem game_step (roster : List Player) (state : channel.State)
    (empty : state.remaining = []) (joint : ∀ who, Option (E.Action who))
    (legal : E.Legal state.history.state joint) :
    (channel.protocol roster).step state ⟨_, channel.game_legal roster state empty joint legal⟩ =
      (E.step state.history.state ⟨joint, legal⟩).bindOnSupport fun target realized =>
        FinDist.pure (channel.advance roster state joint legal target realized) := by
  dsimp only [protocol]
  unfold transition
  split
  · change channel.gameTransition roster state _ =
      channel.gameTransition roster state ⟨joint, legal⟩
    apply congrArg (channel.gameTransition roster state)
    exact Subtype.ext (channel.gameJoint_liftedJoint joint)
  · rename_i actor rest pending
    rw [empty] at pending
    cases pending

def advanceHistory (roster : List Player) (history : (channel.protocol roster).History)
    (empty : history.state.remaining = []) (joint : ∀ who, Option (E.Action who))
    (legal : E.Legal history.state.history.state joint) (target : E.State)
    (realized : target ∈ (E.step history.state.history.state ⟨joint, legal⟩).support) :
    (channel.protocol roster).History :=
  history.extend (channel.game_legal roster history.state empty joint legal)
    (target := channel.advance roster history.state joint legal target realized) (by
      rw [channel.game_step roster history.state empty joint legal, FinDist.support_bindOnSupport]
      exact Set.mem_iUnion.mpr ⟨target, Set.mem_iUnion.mpr
        ⟨realized, FinDist.mem_support_pure.mpr rfl⟩⟩)

/-- Forgetting the communication transcript gives exactly the original game
transition kernel. Evidence emissions do not alter even rejected game results. -/
theorem game_step_map_state (roster : List Player) (state : channel.State)
    (empty : state.remaining = []) (joint : ∀ who, Option (E.Action who))
    (legal : E.Legal state.history.state joint) :
    ((channel.protocol roster).step state
      ⟨_, channel.game_legal roster state empty joint legal⟩).map (fun next => next.history.state) =
        E.step state.history.state ⟨joint, legal⟩ := by
  rw [channel.game_step roster state empty joint legal, FinDist.map_bindOnSupport]
  simp only [FinDist.map_pure]
  change ((E.step state.history.state ⟨joint, legal⟩).bindOnSupport
    fun target _ => FinDist.pure target) = _
  rw [FinDist.bindOnSupport_eq_bind, FinDist.bind_pure]

/-- The evidence emitted along a base history, independently of its game result. -/
def emittedTranscript : {state : E.State} → E.Trace state →
    Communication.Transcript Player channel.Claim channel.Evidence
  | _, .start => []
  | _, .extend (source := before) prior joint legal realized =>
      emittedTranscript prior ++ channel.emissions ⟨before, joint, legal, _, realized⟩

def liftedState {state : E.State} (trace : E.Trace state) : channel.State :=
  ⟨⟨state, trace⟩, [], channel.emittedTranscript trace⟩

/-- With an empty communication roster, every original history remains legal
and acquires exactly its semantic emissions. -/
def liftedTrace : {state : E.State} → (trace : E.Trace state) →
    (channel.protocol []).Trace (channel.liftedState trace)
  | _, .start => .start
  | _, .extend prior joint legal realized =>
      .extend (liftedTrace prior) (channel.liftedJoint joint)
        (channel.game_legal [] (channel.liftedState prior) rfl joint legal) (by
          rw [channel.game_step [] (channel.liftedState prior) rfl joint legal,
            FinDist.support_bindOnSupport]
          exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr
            ⟨realized, FinDist.mem_support_pure.mpr rfl⟩⟩)

def liftHistory (history : E.History) : (channel.protocol []).History :=
  ⟨channel.liftedState history.trace, channel.liftedTrace history.trace⟩

@[simp] theorem liftHistory_history (history : E.History) :
    (channel.liftHistory history).state.history = history := rfl

end Interaction.CommunicationInterface
