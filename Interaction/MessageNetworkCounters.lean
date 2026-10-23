/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkInvariant

/-! # Fresh envelope allocation in the reactive network -/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type} [DecidableEq Principal]

def SerialsBeforeNext (network : MessageNetwork Principal Payload) : Prop :=
  network.Satisfies (fun packet => packet.id.2 < network.nextSerial packet.id.1)

variable {network : MessageNetwork Principal Payload}

omit [DecidableEq Principal] in
theorem SerialsBeforeNext.empty :
    (MessageNetwork.empty : MessageNetwork Principal Payload).SerialsBeforeNext :=
  Satisfies.empty

theorem SerialsBeforeNext.submit (valid : network.SerialsBeforeNext)
    (who : Principal) (payload : Payload) : (network.submit who payload).2.SerialsBeforeNext := by
  have old : network.Satisfies (fun packet =>
      packet.id.2 < (network.submit who payload).2.nextSerial packet.id.1) := by
    apply Satisfies.mono valid
    intro packet earlier
    simp only [MessageNetwork.submit]
    split
    · rename_i same
      rw [same] at earlier
      omega
    · exact earlier
  apply Satisfies.submit old who payload
  simp [MessageNetwork.submit]

theorem SerialsBeforeNext.lookup_next_none (valid : network.SerialsBeforeNext)
    (who : Principal) : network.lookup (who, network.nextSerial who) = none := by
  apply List.find?_eq_none.mpr
  intro message member identified
  have same : message.id = (who, network.nextSerial who) := of_decide_eq_true identified
  have earlier := valid.pending message member
  change message.id.2 < network.nextSerial message.id.1 at earlier
  rw [same] at earlier
  exact Nat.lt_irrefl _ earlier

/-- The newly submitted envelope is found at its fresh authenticated identity. -/
theorem SerialsBeforeNext.lookup_submit (valid : network.SerialsBeforeNext)
    (who : Principal) (payload : Payload) :
    (network.submit who payload).2.lookup (who, network.nextSerial who) =
      some ⟨(who, network.nextSerial who), payload⟩ := by
  have absent := valid.lookup_next_none who
  change network.pending.find? _ = none at absent
  simp only [MessageNetwork.lookup, MessageNetwork.submit, List.find?_append, absent]
  simp

theorem SerialsBeforeNext.learn (valid : network.SerialsBeforeNext)
    (who : Principal) (selected : Finset (MessageId Principal)) :
    (network.learn who selected).SerialsBeforeNext := Satisfies.learn valid who selected

theorem SerialsBeforeNext.includePending (valid : network.SerialsBeforeNext)
    (id : MessageId Principal) : (network.includePending id).2.SerialsBeforeNext := by
  have retained := Satisfies.includePending valid id
  cases found : network.lookup id <;>
    simpa only [SerialsBeforeNext, MessageNetwork.includePending, found] using retained

omit [DecidableEq Principal] in
theorem SerialsBeforeNext.next_unpublished (valid : network.SerialsBeforeNext)
    (who : Principal) : (who, network.nextSerial who) ∉ network.ledger.map Message.id := by
  intro member
  obtain ⟨packet, member, same⟩ := List.mem_map.mp member
  have bound := valid.ledger packet member
  change packet.id.2 < network.nextSerial packet.id.1 at bound
  rw [same] at bound
  exact Nat.lt_irrefl _ bound

end Interaction.MessageNetwork
