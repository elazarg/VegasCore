/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkInvariant
import Interaction.PendingSelection

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

theorem SerialsBeforeNext.replay (valid : network.SerialsBeforeNext)
    (who : Principal) (id : MessageId Principal) :
    (network.replay who id).2.SerialsBeforeNext := by
  have retained := Satisfies.replay valid who id
  cases found : (network.known who).find? (fun envelope => envelope.id = id) <;>
    simpa only [SerialsBeforeNext, MessageNetwork.replay, found] using retained

theorem SerialsBeforeNext.learn (valid : network.SerialsBeforeNext)
    (who : Principal) (selected : Finset (MessageId Principal)) :
    (network.learn who selected).SerialsBeforeNext := Satisfies.learn valid who selected

theorem SerialsBeforeNext.includePending (valid : network.SerialsBeforeNext)
    (id : MessageId Principal) : (network.includePending id).2.SerialsBeforeNext := by
  have retained := Satisfies.includePending valid id
  cases found : network.lookup id <;>
    simpa only [SerialsBeforeNext, MessageNetwork.includePending, found] using retained

/-- No choice of eligibility can make the next identifier an old candidate. -/
theorem SerialsBeforeNext.next_not_eligible (valid : network.SerialsBeforeNext)
    (eligible : Message Principal Payload → Bool) (who : Principal) :
    (who, network.nextSerial who) ∉ eligibleIds eligible network.pending := by
  intro member
  obtain ⟨packet, member, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have bound := valid.pending packet (List.mem_filter.mp member).1
  change packet.id.2 < network.nextSerial packet.id.1 at bound
  rw [same] at bound
  exact Nat.lt_irrefl _ bound

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
