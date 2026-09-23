/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageRetention

/-! # Known envelopes remain pending or published

This is a property of the existing carrier operations, without a scheduler
restriction. Excluding published identifiers from a choice menu consequently
makes every rebroadcast preserve that menu. Publication does not mean that
the application accepted the envelope.
-/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type} [DecidableEq Principal]

def PendingOrPublished (network : MessageNetwork Principal Payload) : Prop :=
  network.RetainsUnsettled (fun packet => packet ∈ network.ledger)

variable {network : MessageNetwork Principal Payload}

omit [DecidableEq Principal] in
theorem PendingOrPublished.empty :
    (MessageNetwork.empty : MessageNetwork Principal Payload).PendingOrPublished :=
  RetainsUnsettled.empty

theorem PendingOrPublished.submit (valid : network.PendingOrPublished)
    (who : Principal) (payload : Payload) : (network.submit who payload).2.PendingOrPublished :=
  RetainsUnsettled.submit valid who payload

theorem PendingOrPublished.replay (valid : network.PendingOrPublished)
    (who : Principal) (id : MessageId Principal) :
    (network.replay who id).2.PendingOrPublished := by
  have retained := RetainsUnsettled.replay valid who id
  cases found : (network.known who).find? (fun envelope => envelope.id = id) <;>
    simpa only [PendingOrPublished, MessageNetwork.replay, found] using retained

theorem PendingOrPublished.learn (valid : network.PendingOrPublished)
    (who : Principal) (selected : Finset (MessageId Principal)) :
    (network.learn who selected).PendingOrPublished :=
  RetainsUnsettled.learn valid who selected

theorem PendingOrPublished.includePending (valid : network.PendingOrPublished)
    (id : MessageId Principal) : (network.includePending id).2.PendingOrPublished := by
  apply RetainsUnsettled.includePending valid id
  · intro packet member
    cases found : network.lookup id with
    | none => simpa [MessageNetwork.includePending, found] using member
    | some selected =>
        simpa only [MessageNetwork.includePending, found] using
          List.mem_append_left [selected] member
  · intro packet found
    simp only [MessageNetwork.includePending, found]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

def unpublished (network : MessageNetwork Principal Payload)
    (eligible : Message Principal Payload → Bool) (packet : Message Principal Payload) : Bool :=
  eligible packet && !(network.ledger.any fun prior => prior.id = packet.id)

/-- Rejected calls count as publications too. -/
def PublishedOnce (network : MessageNetwork Principal Payload) : Prop :=
  (network.ledger.map Message.id).Nodup

omit [DecidableEq Principal] in
theorem PublishedOnce.empty :
    (MessageNetwork.empty : MessageNetwork Principal Payload).PublishedOnce := by
  simp [PublishedOnce, MessageNetwork.empty]

theorem PublishedOnce.submit (valid : network.PublishedOnce)
    (who : Principal) (payload : Payload) : (network.submit who payload).2.PublishedOnce :=
  valid

theorem PublishedOnce.replay (valid : network.PublishedOnce)
    (who : Principal) (id : MessageId Principal) : (network.replay who id).2.PublishedOnce := by
  unfold MessageNetwork.replay
  split <;> exact valid

theorem PublishedOnce.learn (valid : network.PublishedOnce)
    (who : Principal) (selected : Finset (MessageId Principal)) :
    (network.learn who selected).PublishedOnce := valid

theorem PublishedOnce.includePending (valid : network.PublishedOnce)
    (id : MessageId Principal) (fresh : id ∉ network.ledger.map Message.id) :
    (network.includePending id).2.PublishedOnce := by
  cases found : network.lookup id with
  | none => simpa [MessageNetwork.includePending, found] using valid
  | some packet =>
      have same : packet.id = id := by
        simpa using (List.find?_eq_some_iff_append.mp found).1
      simpa [PublishedOnce, MessageNetwork.includePending, found, List.map_append,
        List.nodup_append, same] using And.intro valid fresh

theorem PendingOrPublished.retains_unpublished (valid : network.PendingOrPublished)
    (eligible : Message Principal Payload → Bool) :
    network.RetainsEligible (network.unpublished eligible) := by
  apply RetainsUnsettled.retainsEligible valid
  intro packet member
  have published : (network.ledger.any fun prior => prior.id = packet.id) = true :=
    List.any_eq_true.mpr ⟨packet, member, by simp⟩
  simp [unpublished, published]

theorem PendingOrPublished.replay_unpublished_ids (valid : network.PendingOrPublished)
    (eligible : Message Principal Payload → Bool) (who : Principal) (id : MessageId Principal) :
    eligibleIds ((network.replay who id).2.unpublished eligible)
        (network.replay who id).2.pending =
      eligibleIds (network.unpublished eligible) network.pending := by
  have ledger : (network.replay who id).2.ledger = network.ledger := by
    unfold MessageNetwork.replay
    split <;> rfl
  have predicate : (network.replay who id).2.unpublished eligible =
      network.unpublished eligible := by
    funext packet
    simp only [unpublished, ledger]
  rw [predicate]
  exact (valid.retains_unpublished eligible).replay_ids network _ who id

end Interaction.MessageNetwork
