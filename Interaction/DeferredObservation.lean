/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveQuiescent

/-! # Observation while an owner's message awaits inclusion

Unpublished own envelopes cannot add passive knowledge to their author. Other
players may still learn those envelopes. Inclusion of one pending identifier
also makes every remaining replay of that identifier already published. These
facts retain delayed inclusion, passive leaks, pending multiplicity and recall.
-/

namespace Interaction

open GameTheory.Math.Probability

variable {Principal Payload : Type} [DecidableEq Principal]

/-- An observation sample is inert when every foreign pending envelope is
already known. Pending envelopes authored by the observer need no such premise. -/
theorem MessageNetwork.learn_of_foreign_pending_known
    (network : MessageNetwork Principal Payload) (who : Principal)
    (selected : Finset (MessageId Principal))
    (known : ∀ message ∈ network.pending, message.id.1 ≠ who →
      ∃ prior ∈ network.known who, prior.id = message.id) :
    network.learn who selected = network := by
  have fresh : ((network.pending.map Message.id).eraseDups.filter fun id =>
      id.1 ≠ who ∧ id ∈ selected ∧
        ¬ (network.known who).any (fun message => message.id = id)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro id member
    obtain ⟨message, pending, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp member)
    by_cases foreign : message.id.1 ≠ who
    · obtain ⟨prior, present, same⟩ := known message pending foreign
      have found : (network.known who).any (fun packet => packet.id = message.id) = true :=
        List.any_eq_true.mpr ⟨prior, present, by simp [same]⟩
      simp [found]
    · simp [foreign]
  have same : (fun observer => if observer = who then network.leaked who
      else network.leaked observer) = network.leaked := by
    funext observer
    split <;> simp_all
  simpa only [MessageNetwork.learn, fresh, List.filterMap_nil, List.append_nil] using
    congrArg (fun knowledge => { network with leaked := knowledge }) same

theorem MessageNetwork.learn_of_foreign_pending_published
    (network : MessageNetwork Principal Payload) (who : Principal)
    (selected : Finset (MessageId Principal))
    (published : ∀ message ∈ network.pending, message.id.1 ≠ who →
      message.id ∈ network.ledger.map Message.id) :
    network.learn who selected = network := by
  apply network.learn_of_foreign_pending_known who selected
  intro message member foreign
  obtain ⟨prior, present, same⟩ := List.mem_map.mp (published message member foreign)
  exact ⟨prior, List.mem_append_right _ present, same⟩

/-- This does not restrict what other players can read from the same pool. -/
theorem ReactiveApplication.Execution.activate_of_foreign_pending_published
    (app : ReactiveApplication Principal) (execution : app.Execution) (who : Principal)
    (published : ∀ message ∈ execution.network.pending, message.id.1 ≠ who →
      message.id ∈ execution.network.ledger.map Message.id) :
    execution.environmentStep app (.activate who) =
      PMF.pure { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .activate who⟩] } := by
  simp only [ReactiveApplication.Execution.environmentStep,
    MessageNetwork.learn_of_foreign_pending_published _ _ _ published,
    FinDist.map_const, PMF.pure_map]

/-- A single inclusion publishes the identifier of every remaining replay.
No pending-copy erasure or restriction on who rebroadcast it is assumed. -/
theorem MessageNetwork.include_pending_published_or_selected
    (network : MessageNetwork Principal Payload) (id : MessageId Principal)
    (packet : Message Principal Payload) (found : network.lookup id = some packet)
    (pending : ∀ message ∈ network.pending,
      message.id ∈ network.ledger.map Message.id ∨ message.id = id) :
    ∀ message ∈ (network.includePending id).2.pending,
      message.id ∈ (network.includePending id).2.ledger.map Message.id := by
  have selected : packet.id = id := by
    simpa using (List.find?_eq_some_iff_append.mp found).1
  intro message member
  simp only [MessageNetwork.includePending, found] at member ⊢
  have retained := MessagePool.mem_of_mem_removeFirst id message network.pending member
  rcases pending message retained with old | same
  · exact List.mem_map.mpr (by
      obtain ⟨prior, present, equal⟩ := List.mem_map.mp old
      exact ⟨prior, List.mem_append_left _ present, equal⟩)
  · apply List.mem_map.mpr
    exact ⟨packet, List.mem_append_right _ (by simp), selected.trans same.symm⟩

end Interaction
