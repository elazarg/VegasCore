/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessagePool

/-! # A message network with explicit input history

The network remembers the broadcaster and envelope of each successful input.
Player observations contain inbox and ledger only; own output is retained in
the player's interaction recall. Submission and replay each add one envelope.
Delivery copies an envelope; inclusion consumes one pending copy.
-/

namespace Interaction

structure NetworkInput (Principal Payload : Type) where
  broadcaster : Principal
  envelope : Message Principal Payload

structure MessageNetwork (Principal Payload : Type) where
  pending : List (Message Principal Payload)
  ledger : List (Message Principal Payload)
  inbox : Principal → List (Message Principal Payload)
  inputs : List (NetworkInput Principal Payload)
  nextSerial : Principal → Nat

namespace MessageNetwork

variable {Principal Payload : Type}

def empty : MessageNetwork Principal Payload := ⟨[], [], fun _ => [], [], fun _ => 0⟩

structure PlayerView (Principal Payload : Type) where
  inbox : List (Message Principal Payload)
  ledger : List (Message Principal Payload)

def observe (network : MessageNetwork Principal Payload) (who : Principal) :
    PlayerView Principal Payload := ⟨network.inbox who, network.ledger⟩

variable [DecidableEq Principal]

def lookup (network : MessageNetwork Principal Payload) (id : MessageId Principal) :
    Option (Message Principal Payload) := network.pending.find? (fun packet => packet.id = id)

/-- Eligibility to rebroadcast comes from prior output, receipt, or publication.
This query is used by the network; it is not an extra player observation. -/
def known (network : MessageNetwork Principal Payload) (who : Principal) :
    List (Message Principal Payload) :=
  (network.inputs.filterMap fun input =>
    if input.broadcaster = who then some input.envelope else none) ++
      network.inbox who ++ network.ledger

def submit (network : MessageNetwork Principal Payload) (who : Principal) (payload : Payload) :
    Message Principal Payload × MessageNetwork Principal Payload :=
  let envelope : Message Principal Payload := ⟨(who, network.nextSerial who), payload⟩
  (envelope, { network with
    pending := network.pending ++ [envelope]
    inputs := network.inputs ++ [⟨who, envelope⟩]
    nextSerial := fun observer =>
      if observer = who then network.nextSerial who + 1 else network.nextSerial observer })

def replay (network : MessageNetwork Principal Payload) (who : Principal) (id : MessageId Principal) :
    Option (Message Principal Payload) × MessageNetwork Principal Payload :=
  match (network.known who).find? (fun envelope => envelope.id = id) with
  | none => (none, network)
  | some envelope => (some envelope, { network with
      pending := network.pending ++ [envelope]
      inputs := network.inputs ++ [⟨who, envelope⟩] })

def deliver (network : MessageNetwork Principal Payload) (who : Principal)
    (id : MessageId Principal) : MessageNetwork Principal Payload :=
  match network.lookup id with
  | none => network
  | some envelope => { network with inbox := fun observer =>
      if observer = who then network.inbox who ++ [envelope] else network.inbox observer }

def includePending (network : MessageNetwork Principal Payload) (id : MessageId Principal) :
    Option (Message Principal Payload) × MessageNetwork Principal Payload :=
  match network.lookup id with
  | none => (none, network)
  | some envelope => (some envelope, { network with
      pending := MessagePool.removeFirst id network.pending
      ledger := network.ledger ++ [envelope] })

theorem submit_observe (network : MessageNetwork Principal Payload) (who observer : Principal)
    (payload : Payload) : (network.submit who payload).2.observe observer = network.observe observer :=
  rfl

theorem replay_observe (network : MessageNetwork Principal Payload) (who observer : Principal)
    (id : MessageId Principal) :
    (network.replay who id).2.observe observer = network.observe observer := by
  unfold replay
  split <;> rfl

theorem deliver_pending (network : MessageNetwork Principal Payload) (who : Principal)
    (id : MessageId Principal) : (network.deliver who id).pending = network.pending := by
  unfold deliver
  split <;> rfl

theorem deliver_inbox (network : MessageNetwork Principal Payload) (who : Principal)
    (id : MessageId Principal) (envelope : Message Principal Payload)
    (found : network.lookup id = some envelope) :
    (network.deliver who id).inbox who = network.inbox who ++ [envelope] := by
  simp only [deliver, found, ↓reduceIte]

end MessageNetwork
end Interaction
