/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommunicationProtocol
import GameTheoryExtensions.Protocol.Knowledge

/-! # Evidence soundness throughout a communication game

Every legal communication history has a sound transcript, including after
arbitrary deviations and forwarding. Thus received evidence constrains every
history in the receiver's information set, whether or not that information
set is reached by a prescribed profile.
-/

noncomputable section

namespace Interaction.CommunicationInterface

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open Communication

variable {Player : Type} {E : ExecutionProtocol Player} {M : InformationModel E}
  (channel : CommunicationInterface M)

def State.Sound (state : channel.State) : Prop :=
  channel.evidenceModel.Sound state.history state.transcript

theorem allowed_admissible (state : channel.State) (who : Player) (outgoing : channel.Outgoing)
    (allowed : channel.allowed who (channel.observe state who) outgoing) :
    channel.evidenceModel.Admissible state.history state.transcript
      ⟨who, outgoing.1, outgoing.2⟩ := by
  cases outgoing with
  | mk audience content =>
      cases content <;> exact allowed

theorem communicate_sound (state : channel.State) (sound : state.Sound channel)
    (actor : Player) (rest : List Player) (outgoing : Option channel.Outgoing)
    (allowed : outgoing.elim True (channel.allowed actor (channel.observe state actor))) :
    (channel.communicate state actor rest outgoing).Sound channel := by
  cases outgoing with
  | none => simpa [State.Sound, communicate] using sound
  | some outgoing =>
      exact channel.evidenceModel.sound_append_message _ _ sound _
        (channel.allowed_admissible state actor outgoing allowed)

theorem advance_sound (roster : List Player) (state : channel.State)
    (sound : state.Sound channel) (joint : ∀ who, Option (E.Action who))
    (legal : E.Legal state.history.state joint) (target : E.State)
    (realized : target ∈ (E.step state.history.state ⟨joint, legal⟩).support) :
    (channel.advance roster state joint legal target realized).Sound channel := by
  intro message present fact same
  rcases List.mem_append.mp present with old | emitted
  · exact channel.persists state.history joint legal target realized fact
      (sound message old fact same)
  · exact channel.emissions_sound state.history joint legal target realized
      message emitted fact same

theorem transition_sound (roster : List Player) (state next : channel.State)
    (joint : ∀ who, Option (channel.Action who))
    (running : ¬ E.terminal state.history.state)
    (legal : IsLegalJoint (channel.active state) (channel.available state) joint)
    (sound : state.Sound channel)
    (reached : next ∈ (channel.transition roster state joint running legal).support) :
    next.Sound channel := by
  unfold transition at reached
  split at reached
  next pending =>
      simp only [gameTransition, FinDist.support_bindOnSupport, Set.mem_iUnion] at reached
      obtain ⟨target, realized, same⟩ := reached
      cases FinDist.mem_support_pure.mp same
      exact channel.advance_sound roster state sound _ _ target realized
  next actor rest pending =>
      have own := legal actor
      cases chosen : joint actor with
      | none => simp [chosen, active, pending] at own
      | some action =>
          cases action with
          | inl action => simp [chosen, available, pending] at own
          | inr outgoing =>
              simp only [chosen, Option.bind_some, Sum.elim_inr] at reached
              cases FinDist.mem_support_pure.mp reached
              apply channel.communicate_sound state sound actor rest outgoing
              simpa [chosen, active, available, pending] using own

theorem history_sound (roster : List Player) :
    ∀ {state} (_trace : (channel.protocol roster).Trace state), state.Sound channel
  | _, .start => channel.evidenceModel.sound_nil _
  | _, .extend prior joint legal realized =>
      channel.transition_sound roster _ _ joint legal.1 legal.2
        (history_sound roster prior) realized

/-- The evidence predicate is known at all compatible histories, not merely
true along the intended execution. -/
theorem knows_of_received (roster : List Player) (who : Player)
    (view : (channel.informationModel roster).InfoState who)
    (fact : channel.Evidence)
    (received : ∃ message ∈ view.current.transcript, message.content = .evidence fact) :
    (channel.informationModel roster).Knows who view
      (fun history => channel.valid history.state.history fact) := by
  intro history
  have same := congrArg ObservationRecall.current history.2
  change ((channel.signals roster).infoOf who history.1.trace).current = view.current at same
  rw [channel.info] at same
  have sound : channel.evidenceModel.Sound history.1.state.history history.1.state.transcript :=
    channel.history_sound roster history.1.trace
  exact channel.evidenceModel.valid_at_same_observation history.1.state.history
    history.1.state.transcript sound who
    view.current.transcript (congrArg View.transcript same) fact received

end Interaction.CommunicationInterface
