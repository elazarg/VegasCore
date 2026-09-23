/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.PendingSelection
import GameTheoryExtensions.Math.Probability.PriorityChoice
import GameTheoryExtensions.Core.RegularChoice

/-! # Priority selection over distinct pending messages

Priorities are an explicit input to the service. They include tie breaking and
are held fixed when comparing insertion with silence. The laws below do not
infer priority behavior from miner incentives, or prescribe activation times.
-/

noncomputable section

namespace Interaction.MessageNetwork

open GameTheory GameTheory.Math.Probability

variable {Principal Payload Action : Type} [DecidableEq Principal]

def priorityPending (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload)) :
    FinDist (Option (MessageId Principal)) :=
  PriorityChoice.law priorities (eligibleIds eligible pending)

theorem priorityPending_supported (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload))
    (id : MessageId Principal) (supported : some id ∈
      (priorityPending priorities eligible pending).support) :
    id ∈ eligibleIds eligible pending :=
  PriorityChoice.law_supported priorities _ id supported

/-- Insertion cannot promote any old identifier, including under randomized
priority orders. Arrival order may inform those orders. -/
theorem priorityPending_append_regular
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload))
    (packet : Message Principal Payload) (accepted : eligible packet = true) :
    (priorityPending priorities eligible pending).RegularAt
      (priorityPending priorities eligible (pending ++ [packet])) (some packet.id) := by
  unfold priorityPending
  rw [eligibleIds_append, ite_eq_left accepted]
  exact PriorityChoice.law_regular_insert priorities _ packet.id

theorem priorityPending_submit_regular
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool) (network : MessageNetwork Principal Payload)
    (who : Principal) (payload : Payload)
    (accepted : eligible (network.submit who payload).1 = true) :
    (priorityPending priorities eligible network.pending).RegularAt
      (priorityPending priorities eligible (network.submit who payload).2.pending)
      (some (network.submit who payload).1.id) :=
  priorityPending_append_regular priorities eligible network.pending _ accepted

theorem priorityPending_none_not_supported
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload))
    (nonempty : (eligibleIds eligible pending).Nonempty) :
    none ∉ (priorityPending priorities eligible pending).support :=
  PriorityChoice.law_none_not_supported priorities _ nonempty

/-- An already pending broadcast retains its priority and candidate identity. -/
theorem priorityPending_replay (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool)
    (network next : MessageNetwork Principal Payload) (who : Principal)
    (id : MessageId Principal) (packet : Message Principal Payload)
    (replayed : network.replay who id = (some packet, next))
    (pending : packet ∈ network.pending) :
    priorityPending priorities eligible next.pending =
      priorityPending priorities eligible network.pending := by
  unfold replay at replayed
  split at replayed
  · cases replayed
  · cases replayed
    unfold priorityPending
    rw [eligibleIds_append_existing eligible network.pending packet pending]

theorem priorityPending_learn (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool) (network : MessageNetwork Principal Payload)
    (who : Principal) (selected : Finset (MessageId Principal)) :
    priorityPending priorities eligible (network.learn who selected).pending =
      priorityPending priorities eligible network.pending := rfl

theorem priorityPending_replay_of_retained
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool) (network : MessageNetwork Principal Payload)
    (retained : network.RetainsEligible eligible) (who : Principal) (id : MessageId Principal) :
    priorityPending priorities eligible (network.replay who id).2.pending =
      priorityPending priorities eligible network.pending := by
  unfold priorityPending
  rw [retained.replay_ids]

/-- Decode candidate identities only after selection. The decoder is total;
the nonempty old menu excludes an invented source action for no selection. -/
def priorityProposal (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload))
    (nonempty : (eligibleIds eligible pending).Nonempty)
    (packet : Message Principal Payload) (accepted : eligible packet = true)
    (fresh : packet.id ∉ eligibleIds eligible pending)
    (decode : MessageId Principal → Action) : PendingChoice.RegularSelection Action :=
  PendingChoice.RegularSelection.ofInsertion
    (priorityPending priorities eligible pending)
    (priorityPending priorities eligible (pending ++ [packet])) (some packet.id)
    (fun supported => fresh
      (priorityPending_supported priorities eligible pending packet.id supported))
    (priorityPending_append_regular priorities eligible pending packet accepted)
    (fun selected => decode (selected.getD nonempty.choose))

end Interaction.MessageNetwork
