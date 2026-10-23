/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

/-! # A minimal native message pool

Messages carry sender-local identifiers. Submission records a pending message;
delivery copies an existing pending message into a selected observer's local
inbox; inclusion removes an existing pending message and appends it to the
public ledger. Neither delivery nor inclusion invokes a sender callback.

Any observer may receive any pending message. The published ledger is a shared
observation in this model; pending delivery is recipient-local. Sender fields
are raw labels and provide no authentication. Sent lists record the sender's
authored submissions. The carrier adds no clocks or service guarantees.
-/

namespace Interaction

universe uPrincipal uPayload

abbrev MessageId (Principal : Type uPrincipal) := Principal × Nat

structure Message (Principal : Type uPrincipal) (Payload : Type uPayload) where
  id : MessageId Principal
  payload : Payload

def Message.sender {Principal : Type uPrincipal} {Payload : Type uPayload}
    (message : Message Principal Payload) : Principal :=
  message.id.1

structure MessagePool (Principal : Type uPrincipal) (Payload : Type uPayload) where
  pending : List (Message Principal Payload)
  ledger : List (Message Principal Payload)
  inbox : Principal → List (Message Principal Payload)
  sent : Principal → List (Message Principal Payload)
  nextSerial : Principal → Nat

namespace MessagePool

def empty (Principal : Type uPrincipal) (Payload : Type uPayload) :
    MessagePool Principal Payload where
  pending := []
  ledger := []
  inbox := fun _ => []
  sent := fun _ => []
  nextSerial := fun _ => 0

structure Result (Principal : Type uPrincipal) (Payload : Type uPayload) where
  message : Option (Message Principal Payload)
  state : MessagePool Principal Payload

def Result.invalid {Principal : Type uPrincipal} {Payload : Type uPayload}
    (state : MessagePool Principal Payload) : Result Principal Payload :=
  ⟨none, state⟩

variable {Principal : Type uPrincipal} {Payload : Type uPayload}
variable [DecidableEq Principal]

def submit (state : MessagePool Principal Payload) (sender : Principal)
    (payload : Payload) : MessageId Principal × MessagePool Principal Payload :=
  let id := (sender, state.nextSerial sender)
  let message : Message Principal Payload := ⟨id, payload⟩
  (id, {
    state with
    pending := state.pending ++ [message]
    sent := fun who => if who = sender then state.sent sender ++ [message] else state.sent who
    nextSerial := fun who =>
      if who = sender then state.nextSerial sender + 1 else state.nextSerial who })

def lookup (state : MessagePool Principal Payload) (id : MessageId Principal) :
    Option (Message Principal Payload) :=
  state.pending.find? fun message => message.id = id

def removeFirst (id : MessageId Principal) :
    List (Message Principal Payload) → List (Message Principal Payload)
  | [] => []
  | message :: rest =>
      if message.id = id then rest else message :: removeFirst id rest

def deliver (state : MessagePool Principal Payload) (observer : Principal)
    (id : MessageId Principal) : Result Principal Payload :=
  match state.lookup id with
  | some message =>
      ⟨some message, {
        state with
        inbox := fun who =>
          if who = observer then state.inbox observer ++ [message] else state.inbox who }⟩
  | none => Result.invalid state

def includePending (state : MessagePool Principal Payload) (id : MessageId Principal) :
    Result Principal Payload :=
  match state.lookup id with
  | some message =>
      ⟨some message, {
        state with
        pending := removeFirst id state.pending
        ledger := state.ledger ++ [message] }⟩
  | none => Result.invalid state

structure View (Principal : Type uPrincipal) (Payload : Type uPayload) where
  inbox : List (Message Principal Payload)
  ledger : List (Message Principal Payload)
  sent : List (Message Principal Payload)

def observe (state : MessagePool Principal Payload) (who : Principal) :
    View Principal Payload :=
  ⟨state.inbox who, state.ledger, state.sent who⟩

theorem removeFirst_length_of_find (id : MessageId Principal)
    (messages : List (Message Principal Payload)) (message : Message Principal Payload)
    (hfind : messages.find? (fun candidate => candidate.id = id) = some message) :
    (removeFirst id messages).length + 1 = messages.length := by
  induction messages with
  | nil => simp at hfind
  | cons first rest ih =>
      by_cases hfirst : first.id = id
      · simp [removeFirst, hfirst]
      · have hrest : rest.find? (fun candidate => candidate.id = id) = some message := by
          simpa [List.find?, hfirst] using hfind
        simpa [removeFirst, hfirst, Nat.add_assoc] using congrArg Nat.succ (ih hrest)

end MessagePool

end Interaction
