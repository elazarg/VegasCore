/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork

/-! # Observation of already published traffic

Pending envelopes whose identifiers are already on the ledger add no private
knowledge, under any observation rule. Replaying such an envelope preserves this
property. These facts do not erase network inputs or action recall and do not
assert that arbitrary schedulers ignore rebroadcasts.
-/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type} [DecidableEq Principal]

/-- Sampling cannot reveal a new packet when every pending identifier is known. -/
theorem learn_of_pending_known (network : MessageNetwork Principal Payload)
    (who : Principal) (selected : Finset (MessageId Principal))
    (known : ∀ message ∈ network.pending,
      ∃ prior ∈ network.known who, prior.id = message.id) :
    network.learn who selected = network := by
  have fresh : ((network.pending.map Message.id).eraseDups.filter fun id =>
      id.1 ≠ who ∧ id ∈ selected ∧
        ¬ (network.known who).any (fun message => message.id = id)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro id member
    obtain ⟨message, pending, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp member)
    obtain ⟨prior, present, same⟩ := known message pending
    have found : (network.known who).any (fun packet => packet.id = message.id) = true :=
      List.any_eq_true.mpr ⟨prior, present, by simp [same]⟩
    simp [found]
  have same : (fun observer => if observer = who then network.leaked who
      else network.leaked observer) = network.leaked := by
    funext observer
    split <;> simp_all
  simpa only [learn, fresh, List.filterMap_nil, List.append_nil] using
    congrArg (fun knowledge => { network with leaked := knowledge }) same

/-- Publication includes rejected calls: the identifier alone prevents relearning. -/
theorem learn_of_pending_published (network : MessageNetwork Principal Payload)
    (who : Principal) (selected : Finset (MessageId Principal))
    (published : ∀ message ∈ network.pending, message.id ∈ network.ledger.map Message.id) :
    network.learn who selected = network := by
  apply learn_of_pending_known
  intro message member
  obtain ⟨prior, present, same⟩ := List.mem_map.mp (published message member)
  exact ⟨prior, List.mem_append_right _ present, same⟩

/-- Rebroadcasting a published identifier cannot introduce unpublished pending
traffic, even if the known list contains duplicate identifiers. -/
theorem replay_pending_published (network : MessageNetwork Principal Payload)
    (who : Principal) (id : MessageId Principal)
    (published : ∀ message ∈ network.pending, message.id ∈ network.ledger.map Message.id)
    (spent : id ∈ network.ledger.map Message.id) :
    ∀ message ∈ (network.replay who id).2.pending,
      message.id ∈ (network.replay who id).2.ledger.map Message.id := by
  cases found : (network.known who).find? (fun packet => packet.id = id) with
  | none => simpa only [replay, found] using published
  | some packet =>
      have same : packet.id = id := by
        simpa using (List.find?_eq_some_iff_append.mp found).1
      intro message member
      simp only [replay, found] at member ⊢
      rcases List.mem_append.mp member with prior | added
      · exact published message prior
      · obtain rfl := List.mem_singleton.mp added
        simpa only [same] using spent

end Interaction.MessageNetwork
