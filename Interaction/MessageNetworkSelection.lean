/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork

/-! # Pending network envelopes persist unless selected for inclusion -/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type} [DecidableEq Principal]

/-- Inclusion removes no other pending envelope. The statement is inherited
from the actual message-pool operation used by the network. -/
theorem pending_retained_or_selected (network : MessageNetwork Principal Payload)
    (identifier : MessageId Principal) (message : Message Principal Payload)
    (member : message ∈ network.pending) :
    message ∈ (network.includePending identifier).2.pending ∨
      network.lookup identifier = some message := by
  let pool : MessagePool Principal Payload :=
    ⟨network.pending, network.ledger, fun _ => [], fun _ => [], network.nextSerial⟩
  have retained := pool.pending_retained_or_selected identifier message member
  cases found : network.pending.find? (fun packet => packet.id = identifier) <;>
    simpa only [MessagePool.includePending, MessagePool.lookup, MessageNetwork.includePending,
      MessageNetwork.lookup, MessagePool.Result.invalid, pool, found] using retained

end Interaction.MessageNetwork
