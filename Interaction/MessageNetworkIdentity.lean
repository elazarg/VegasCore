/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkCounters

/-! # An envelope identifier fixes the entire message

Fresh submission allocates a new identifier. Observation, replay and inclusion
copy existing envelopes, so they cannot introduce different payloads under one
identifier. Multiple copies of the same envelope remain unrestricted.
-/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type}

def UniqueIds (network : MessageNetwork Principal Payload) : Prop :=
  network.Satisfies fun message => network.Satisfies fun other =>
    other.id = message.id → other = message

variable {network : MessageNetwork Principal Payload}

theorem UniqueIds.empty : (MessageNetwork.empty : MessageNetwork Principal Payload).UniqueIds :=
  Satisfies.empty

variable [DecidableEq Principal]

theorem UniqueIds.replay (valid : network.UniqueIds) (who : Principal) (id : MessageId Principal) :
    (network.replay who id).2.UniqueIds :=
  (valid.mono fun _ matching => matching.replay who id).replay who id

theorem UniqueIds.learn (valid : network.UniqueIds) (who : Principal)
    (selected : Finset (MessageId Principal)) : (network.learn who selected).UniqueIds :=
  (valid.mono fun _ matching => matching.learn who selected).learn who selected

theorem UniqueIds.includePending (valid : network.UniqueIds) (id : MessageId Principal) :
    (network.includePending id).2.UniqueIds :=
  (valid.mono fun _ matching => matching.includePending id).includePending id

theorem UniqueIds.submit (valid : network.UniqueIds) (serials : network.SerialsBeforeNext)
    (who : Principal) (payload : Payload) : (network.submit who payload).2.UniqueIds := by
  let issued : Message Principal Payload := ⟨(who, network.nextSerial who), payload⟩
  have fresh : network.Satisfies fun message => message.id ≠ issued.id := by
    apply serials.mono
    intro message earlier same
    change message.id.2 < network.nextSerial message.id.1 at earlier
    rw [same] at earlier
    exact Nat.lt_irrefl _ earlier
  have old : network.Satisfies fun message => (network.submit who payload).2.Satisfies
      fun other => other.id = message.id → other = message :=
    (valid.and fresh).mono fun _ pair => pair.1.submit who payload
      (fun same => False.elim (pair.2 same.symm))
  apply old.submit who payload
  apply (fresh.mono fun _ different same => False.elim (different same)).submit who payload
  exact fun _ => rfl

/-- When a known identifier is already public, the very same envelope is in
the ledger. Equality of identifiers cannot conceal a different certificate. -/
theorem UniqueIds.known_published (valid : network.UniqueIds) (who : Principal)
    (message : Message Principal Payload) (known : message ∈ network.known who)
    (published : message.id ∈ network.ledger.map Message.id) : message ∈ network.ledger := by
  obtain ⟨record, present, same⟩ := List.mem_map.mp published
  have equal := (valid.known who message known).ledger record present same
  exact equal ▸ present

end Interaction.MessageNetwork
