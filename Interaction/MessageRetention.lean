/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkInvariant
import Interaction.PendingSelection

/-! # Retaining envelopes until their purpose is settled

An envelope may leave pending while remaining known. The invariant below
requires every such envelope to satisfy a supplied settlement predicate.
Publication is one such predicate, independent of application acceptance.
-/

namespace Interaction

variable {Principal Payload : Type} [DecidableEq Principal]

namespace MessagePool

theorem mem_removeFirst_or_found (id : MessageId Principal)
    (messages : List (Message Principal Payload)) (packet : Message Principal Payload)
    (member : packet ∈ messages) :
    packet ∈ removeFirst id messages ∨
      messages.find? (fun candidate => candidate.id = id) = some packet := by
  induction messages with
  | nil => simp at member
  | cons first rest ih =>
      by_cases same : first.id = id
      · rcases List.mem_cons.mp member with rfl | later
        · exact Or.inr (by simp [same])
        · exact Or.inl (by simpa [removeFirst, same] using later)
      · rcases List.mem_cons.mp member with rfl | later
        · exact Or.inl (by simp [removeFirst, same])
        · rcases ih later with retained | found
          · exact Or.inl (by simp [removeFirst, same, retained])
          · exact Or.inr (by simpa [same] using found)

end MessagePool

namespace MessageNetwork

/-- All recorded envelopes remain pending unless they satisfy the settlement predicate. -/
def RetainsUnsettled (network : MessageNetwork Principal Payload)
    (settled : Message Principal Payload → Prop) : Prop :=
  network.Satisfies (fun packet => packet ∈ network.pending ∨ settled packet)

variable {network : MessageNetwork Principal Payload}
  {settled later : Message Principal Payload → Prop}

omit [DecidableEq Principal] in
theorem RetainsUnsettled.empty :
    (MessageNetwork.empty : MessageNetwork Principal Payload).RetainsUnsettled settled :=
  Satisfies.empty

omit [DecidableEq Principal] in
theorem RetainsUnsettled.mono (retained : network.RetainsUnsettled settled)
    (persists : ∀ packet, settled packet → later packet) :
    network.RetainsUnsettled later :=
  Satisfies.mono retained (fun packet => Or.imp_right (persists packet))

theorem RetainsUnsettled.submit (retained : network.RetainsUnsettled settled)
    (who : Principal) (payload : Payload) :
    (network.submit who payload).2.RetainsUnsettled settled := by
  apply Satisfies.submit (safe := fun packet =>
    packet ∈ (network.submit who payload).2.pending ∨ settled packet)
  · exact Satisfies.mono retained fun _ located => located.imp_left (List.mem_append_left _)
  · exact Or.inl (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem RetainsUnsettled.replay (retained : network.RetainsUnsettled settled)
    (who : Principal) (id : MessageId Principal) :
    (network.replay who id).2.RetainsUnsettled settled := by
  unfold MessageNetwork.replay
  split
  · exact retained
  · rename_i packet found
    have widened : network.Satisfies (fun candidate =>
        candidate ∈ network.pending ++ [packet] ∨ settled candidate) :=
      Satisfies.mono retained fun _ located => located.imp_left (List.mem_append_left _)
    have result := widened.replay who id
    simpa only [RetainsUnsettled, MessageNetwork.replay, found] using result

theorem RetainsUnsettled.learn (retained : network.RetainsUnsettled settled)
    (who : Principal) (selected : Finset (MessageId Principal)) :
    (network.learn who selected).RetainsUnsettled settled :=
  Satisfies.learn retained who selected

/-- Inclusion is safe when the removed envelope is settled afterward and
previously settled envelopes remain settled. Duplicate identifiers need not
be ruled out for this carrier-level result. -/
theorem RetainsUnsettled.includePending (retained : network.RetainsUnsettled settled)
    (id : MessageId Principal) (persists : ∀ packet, settled packet → later packet)
    (settles : ∀ packet, network.lookup id = some packet → later packet) :
    (network.includePending id).2.RetainsUnsettled later := by
  apply Satisfies.includePending (safe := fun packet =>
    packet ∈ (network.includePending id).2.pending ∨ later packet)
  apply Satisfies.mono retained
  intro packet located
  rcases located with pending | done
  · cases found : network.lookup id with
    | none => exact Or.inl (by simpa [MessageNetwork.includePending, found] using pending)
    | some selected =>
        rcases MessagePool.mem_removeFirst_or_found id network.pending packet pending with
          kept | selectedPacket
        · exact Or.inl (by simpa [MessageNetwork.includePending, found] using kept)
        · exact Or.inr (settles packet selectedPacket)
  · exact Or.inr (persists packet done)

/-- Settled envelopes must be outside the current choice menu. -/
theorem RetainsUnsettled.retainsEligible (retained : network.RetainsUnsettled settled)
    (eligible : Message Principal Payload → Bool)
    (excluded : ∀ packet, settled packet → eligible packet = false) :
    network.RetainsEligible eligible := by
  intro who packet known accepted
  rcases retained.known who packet known with pending | done
  · simp only [eligibleIds, List.mem_toFinset, List.mem_map]
    exact ⟨packet, List.mem_filter.mpr ⟨pending, accepted⟩, rfl⟩
  · have impossible := (excluded packet done).symm.trans accepted
    cases impossible

end MessageNetwork
end Interaction
