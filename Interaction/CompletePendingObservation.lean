/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageMonitoring
import Interaction.MessageNetworkIdentity

noncomputable section

/-! # Complete observation of retained network traffic

Selecting every pending identifier exposes every foreign submitted envelope:
the carrier retains it in pending or publishes it in the ledger. Publication
includes rejected application calls. The result uses the player's ordinary
leaked-and-ledger view, without access to the carrier's input log.
-/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type} [DecidableEq Principal]

/-- A public packet observer selects every currently pending identifier. -/
def completePendingObservation : ObservationRule Principal Payload :=
  fun _ pending => PMF.pure (pending.map Message.id).toFinset

instance completePendingObservation_finiteSupport :
    ObservationRule.FiniteSupport
      (completePendingObservation (Principal := Principal) (Payload := Payload)) where
  support_finite := by
    intro who pending
    simp [completePendingObservation]

/-- Selected foreign pending material becomes ordinary observation material,
including when the observer already knows an envelope with its identifier. -/
theorem selected_pending_visible (network : MessageNetwork Principal Payload)
    (unique : network.UniqueIds) (who : Principal)
    (selected : Finset (MessageId Principal)) (message : Message Principal Payload)
    (pending : message ∈ network.pending) (foreign : message.sender ≠ who)
    (chosen : message.id ∈ selected) :
    message ∈ ((network.learn who selected).observe who).leaked ∨
      message ∈ ((network.learn who selected).observe who).ledger := by
  by_cases known : (network.known who).any (fun packet => packet.id = message.id) = true
  · obtain ⟨prior, present, same⟩ := List.any_eq_true.mp known
    have equal : prior = message :=
      (unique.pending message pending).known who prior present (by simpa using same)
    subst prior
    simp only [MessageNetwork.known, List.mem_append] at present
    rcases present with (own | leaked) | included
    · have ownAuthor := (List.mem_filter.mp own).2
      have : message.sender = who := by simpa using ownAuthor
      exact False.elim (foreign this)
    · left
      simp only [observe, learn, ↓reduceIte]
      exact List.mem_append_left _ leaked
    · exact Or.inr included
  · have unknown : (network.known who).any (fun packet => packet.id = message.id) = false :=
      Bool.eq_false_of_not_eq_true known
    cases found : network.lookup message.id with
    | none =>
        have absent := List.find?_eq_none.mp found message pending
        simp at absent
    | some prior =>
        have same : prior.id = message.id := by
          simpa using (List.find?_eq_some_iff_append.mp found).1
        have equal : prior = message :=
          (unique.pending message pending).lookup message.id prior found same
        subst prior
        have reported := network.reports_learn_selected (fun _ => true) who selected
          message.id message found foreign chosen unknown rfl
        exact ((PlayerView.mem_reports ..).mp reported).1

/-- Under complete pending observation every foreign submitted envelope is
visible, whether it remains pending or has been included and rejected. -/
theorem submitted_visible_of_complete_observation
    (network : MessageNetwork Principal Payload) (unique : network.UniqueIds)
    (retained : network.PendingOrPublished) (who : Principal)
    (message : Message Principal Payload) (submitted : message ∈ network.inputs)
    (foreign : message.sender ≠ who) :
    message ∈ ((network.learn who (network.pending.map Message.id).toFinset).observe who).leaked ∨
      message ∈
        ((network.learn who (network.pending.map Message.id).toFinset).observe who).ledger := by
  rcases retained.inputs message submitted with pending | published
  · apply selected_pending_visible network unique who _ message pending foreign
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨message, pending, rfl⟩)
  · exact Or.inr published

end Interaction.MessageNetwork
