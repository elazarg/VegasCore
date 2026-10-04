/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork
import Interaction.MessageNetworkCounters

/-! # Observation of already published traffic

Pending envelopes whose identifiers are already on the ledger add no private
knowledge, under any observation rule. These facts do not erase network inputs
or action recall.
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

/-- Own output history contributes no hidden packet at a checkpoint where
every input and every leaked identifier has already been published. -/
theorem known_published (network : MessageNetwork Principal Payload) (who : Principal)
    (inputs : ∀ input ∈ network.inputs, input.id ∈ network.ledger.map Message.id)
    (leaked : ∀ message ∈ network.leaked who, message.id ∈ network.ledger.map Message.id) :
    ∀ message ∈ network.known who, message.id ∈ network.ledger.map Message.id := by
  intro message member
  rcases List.mem_append.mp member with ownOrLeaked | published
  · rcases List.mem_append.mp ownOrLeaked with own | observed
    · exact inputs message (List.mem_filter.mp own).1
    · exact leaked message observed
  · exact List.mem_map.mpr ⟨message, published, rfl⟩

/-- Including the fresh envelope immediately after submission restores a
published-only checkpoint, retaining the new input. -/
theorem submit_include_published (network : MessageNetwork Principal Payload)
    (who : Principal) (payload : Payload)
    (pending : ∀ message ∈ network.pending, message.id ∈ network.ledger.map Message.id)
    (inputs : ∀ input ∈ network.inputs, input.id ∈ network.ledger.map Message.id)
    (serials : network.SerialsBeforeNext) :
    let next := ((network.submit who payload).2.includePending (who, network.nextSerial who)).2
    (∀ message ∈ next.pending, message.id ∈ next.ledger.map Message.id) ∧
      (∀ input ∈ next.inputs, input.id ∈ next.ledger.map Message.id) ∧
      next.leaked = network.leaked ∧ next.SerialsBeforeNext := by
  dsimp only
  have found := serials.lookup_submit who payload
  refine ⟨?_, ?_, ?_, (serials.submit who payload).includePending _⟩
  · intro message member
    simp only [includePending, found] at member ⊢
    simp only [submit, List.map_append, List.map_singleton] at member ⊢
    have retained := MessagePool.mem_of_mem_removeFirst _ message _ member
    rcases List.mem_append.mp retained with prior | added
    · exact List.mem_append_left _ (pending message prior)
    · obtain rfl := List.mem_singleton.mp added
      exact List.mem_append_right _ (by simp)
  · intro input member
    simp only [includePending, found] at member ⊢
    simp only [submit, List.map_append, List.map_singleton] at member ⊢
    rcases List.mem_append.mp member with prior | added
    · exact List.mem_append_left _ (inputs input prior)
    · obtain rfl := List.mem_singleton.mp added
      exact List.mem_append_right _ (by simp)
  · simp only [includePending, found]
    rfl

end Interaction.MessageNetwork
