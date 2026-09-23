/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessagePool
import GameTheory.Math.Probability.FinDist

/-! # A message network with explicit input history

The network remembers the broadcaster and envelope of each successful input.
Player observations contain leaked packets and the ledger; own output is
retained in interaction recall. Passive observation can add knowledge of other
authors' pending packets. It does not change the network's public state.
-/

namespace Interaction

structure NetworkInput (Principal Payload : Type) where
  broadcaster : Principal
  envelope : Message Principal Payload

structure MessageNetwork (Principal Payload : Type) where
  pending : List (Message Principal Payload)
  ledger : List (Message Principal Payload)
  leaked : Principal → List (Message Principal Payload)
  inputs : List (NetworkInput Principal Payload)
  nextSerial : Principal → Nat

namespace MessageNetwork

variable {Principal Payload : Type}

def empty : MessageNetwork Principal Payload := ⟨[], [], fun _ => [], [], fun _ => 0⟩

structure PublicView (Principal Payload : Type) where
  pending : List (Message Principal Payload)
  ledger : List (Message Principal Payload)
  inputs : List (NetworkInput Principal Payload)
  nextSerial : Principal → Nat

def publicView (network : MessageNetwork Principal Payload) : PublicView Principal Payload :=
  ⟨network.pending, network.ledger, network.inputs, network.nextSerial⟩

/-- A separate, stateless observation kernel selects a finite subset of pending
identifiers. Its sample is private to the observer and is never scheduler recall. -/
abbrev ObservationRule (Principal Payload : Type) :=
  Principal → List (Message Principal Payload) →
    GameTheory.Math.Probability.FinDist (Finset (MessageId Principal))

structure PlayerView (Principal Payload : Type) where
  leaked : List (Message Principal Payload)
  ledger : List (Message Principal Payload)

def observe (network : MessageNetwork Principal Payload) (who : Principal) :
    PlayerView Principal Payload := ⟨network.leaked who, network.ledger⟩

variable [DecidableEq Principal]

def lookup (network : MessageNetwork Principal Payload) (id : MessageId Principal) :
    Option (Message Principal Payload) := network.pending.find? (fun packet => packet.id = id)

/-- Eligibility to rebroadcast comes from prior output, receipt, or publication.
This query is used by the network; it is not an extra player observation. -/
def known (network : MessageNetwork Principal Payload) (who : Principal) :
    List (Message Principal Payload) :=
  (network.inputs.filterMap fun input =>
    if input.broadcaster = who then some input.envelope else none) ++
      network.leaked who ++ network.ledger

def submit (network : MessageNetwork Principal Payload) (who : Principal) (payload : Payload) :
    Message Principal Payload × MessageNetwork Principal Payload :=
  let envelope : Message Principal Payload := ⟨(who, network.nextSerial who), payload⟩
  (envelope, { network with
    pending := network.pending ++ [envelope]
    inputs := network.inputs ++ [⟨who, envelope⟩]
    nextSerial := fun observer =>
      if observer = who then network.nextSerial who + 1 else network.nextSerial observer })

def replay (network : MessageNetwork Principal Payload) (who : Principal)
    (id : MessageId Principal) :
    Option (Message Principal Payload) × MessageNetwork Principal Payload :=
  match (network.known who).find? (fun envelope => envelope.id = id) with
  | none => (none, network)
  | some envelope => (some envelope, { network with
      pending := network.pending ++ [envelope]
      inputs := network.inputs ++ [⟨who, envelope⟩] })

/-- Learn only fresh knowledge of other authors' pending envelopes. Sampling
an own, known, duplicate, or nonpending identifier produces no extra observation. -/
def learn (network : MessageNetwork Principal Payload) (who : Principal)
    (selected : Finset (MessageId Principal)) : MessageNetwork Principal Payload :=
  let fresh := (network.pending.map Message.id).eraseDups.filter fun id =>
    id.1 ≠ who ∧ id ∈ selected ∧ ¬ (network.known who).any (fun message => message.id = id)
  { network with leaked := fun observer => if observer = who then
      network.leaked who ++ fresh.filterMap network.lookup else network.leaked observer }

def includePending (network : MessageNetwork Principal Payload) (id : MessageId Principal) :
    Option (Message Principal Payload) × MessageNetwork Principal Payload :=
  match network.lookup id with
  | none => (none, network)
  | some envelope => (some envelope, { network with
      pending := MessagePool.removeFirst id network.pending
      ledger := network.ledger ++ [envelope] })

theorem submit_observe (network : MessageNetwork Principal Payload) (who observer : Principal)
    (payload : Payload) :
    (network.submit who payload).2.observe observer = network.observe observer :=
  rfl

theorem replay_observe (network : MessageNetwork Principal Payload) (who observer : Principal)
    (id : MessageId Principal) :
    (network.replay who id).2.observe observer = network.observe observer := by
  unfold replay
  split <;> rfl

theorem learn_publicView (network : MessageNetwork Principal Payload) (who : Principal)
    (selected : Finset (MessageId Principal)) :
    (network.learn who selected).publicView = network.publicView := rfl

@[simp] theorem learn_empty (network : MessageNetwork Principal Payload) (who : Principal) :
    network.learn who ∅ = network := by
  have same : (fun observer => if observer = who then network.leaked who
      else network.leaked observer) = network.leaked := by
    funext observer
    split <;> simp_all
  simpa [learn] using congrArg (fun knowledge => { network with leaked := knowledge }) same

theorem learn_other (network : MessageNetwork Principal Payload) (who observer : Principal)
    (selected : Finset (MessageId Principal)) (different : observer ≠ who) :
    (network.learn who selected).leaked observer = network.leaked observer := by
  simp only [learn, ite_eq_right different]

theorem learn_mem (network : MessageNetwork Principal Payload) (who : Principal)
    (selected : Finset (MessageId Principal)) (message : Message Principal Payload)
    (member : message ∈ (network.learn who selected).leaked who) :
    message ∈ network.leaked who ∨
      (message ∈ network.pending ∧ message.sender ≠ who) := by
  simp only [learn, ↓reduceIte, List.mem_append] at member
  rcases member with prior | fresh
  · exact Or.inl prior
  · obtain ⟨id, member, found⟩ := List.mem_filterMap.mp fresh
    have chosen := (List.mem_filter.mp member).2
    have identified := (List.find?_eq_some_iff_append.mp found).1
    have same : message.id = id := by simpa using identified
    have foreign : id.1 ≠ who := (of_decide_eq_true chosen).1
    exact Or.inr ⟨List.mem_of_find?_eq_some found, by simpa [Message.sender, same] using foreign⟩

end MessageNetwork
end Interaction
