/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveApplication

/-! # Erasing one envelope from the environment's input

The environment's input is its command recall and its current view. Erasing an
envelope produces the input of the world in which that envelope was never
sent: the envelope leaves every recorded pending list, ledger and input list,
its receipts disappear, and its author's later identifiers, its next serial and
every recorded inclusion command naming them move down by one. Restoring maps an
identifier of the erased world back to the original one.

Erasure is a statement about inputs only; whether a scheduler ignores an erased
envelope is a property stated elsewhere.
-/

namespace Interaction

variable {Principal : Type} [DecidableEq Principal]

namespace MessageId

/-- The identifier in the world without `removed`: the author's later
identifiers move down by one. -/
def erase (removed id : MessageId Principal) : MessageId Principal :=
  if id.1 = removed.1 ∧ removed.2 < id.2 then (id.1, id.2 - 1) else id

/-- The original identifier of an identifier of the world without `removed`. -/
def restore (removed id : MessageId Principal) : MessageId Principal :=
  if id.1 = removed.1 ∧ removed.2 ≤ id.2 then (id.1, id.2 + 1) else id

theorem restore_erase (removed id : MessageId Principal) (kept : id ≠ removed) :
    restore removed (erase removed id) = id := by
  rcases id with ⟨author, serial⟩
  rcases removed with ⟨who, gone⟩
  unfold erase restore
  by_cases later : author = who ∧ gone < serial
  · have restoredHere : author = who ∧ gone ≤ serial - 1 := ⟨later.1, by omega⟩
    simp only [later, and_self, ↓reduceIte, restoredHere]
    exact Prod.ext rfl (by dsimp only; omega)
  · simp only [later, ↓reduceIte]
    by_cases same : author = who
    · have earlier : serial < gone := by
        rcases Nat.lt_or_ge serial gone with below | above
        · exact below
        · rcases Nat.lt_or_eq_of_le above with strict | equal
          · exact absurd ⟨same, strict⟩ later
          · exact absurd (Prod.ext same equal.symm) kept
      have notRestored : ¬ (author = who ∧ gone ≤ serial) := fun both => by omega
      simp only [notRestored, ↓reduceIte]
    · have notRestored : ¬ (author = who ∧ gone ≤ serial) := fun both => same both.1
      simp only [notRestored, ↓reduceIte]

end MessageId

variable {Payload : Type}

namespace Message

/-- Drop the envelope `removed` from a list and rename the author's later
envelopes. -/
def eraseList (removed : MessageId Principal) (messages : List (Message Principal Payload)) :
    List (Message Principal Payload) :=
  (messages.filter fun message => message.id ≠ removed).map fun message =>
    ⟨MessageId.erase removed message.id, message.payload⟩

end Message

namespace MessageNetwork.PublicView

/-- The public network view of the world without `removed`. -/
def erase (removed : MessageId Principal) (view : PublicView Principal Payload) :
    PublicView Principal Payload where
  pending := Message.eraseList removed view.pending
  ledger := Message.eraseList removed view.ledger
  inputs := Message.eraseList removed view.inputs
  nextSerial := fun who => if who = removed.1 then view.nextSerial who - 1 else view.nextSerial who

end MessageNetwork.PublicView

namespace ReactiveApplication

variable (app : ReactiveApplication Principal)

/-- Receipts of the world without `removed`. -/
def eraseReceipts (removed : MessageId Principal) (receipts : List (MessageId Principal × Bool)) :
    List (MessageId Principal × Bool) :=
  (receipts.filter fun receipt => receipt.1 ≠ removed).map fun receipt =>
    (MessageId.erase removed receipt.1, receipt.2)

/-- The environment view of the world without `removed`. The application's
public observation is kept: it is the caller's obligation that `removed` did
not change it. -/
def EnvironmentView.erase (removed : MessageId Principal) (view : app.EnvironmentView) :
    app.EnvironmentView where
  network := view.network.erase removed
  application := view.application
  receipts := eraseReceipts removed view.receipts

/-- A command of the world without `removed`, read in that world. -/
def Command.erase (removed : MessageId Principal) : app.Command → app.Command
  | .include id => .include (MessageId.erase removed id)
  | command => command

/-- A command chosen in the world without `removed`, read in the original
world. -/
def Command.restore (removed : MessageId Principal) : app.Command → app.Command
  | .include id => .include (MessageId.restore removed id)
  | command => command

/-- The command recall of the world without `removed`. -/
def eraseEnvironmentRecall (removed : MessageId Principal)
    (recall : List app.EnvironmentEntry) : List app.EnvironmentEntry :=
  recall.map fun entry => ⟨EnvironmentView.erase app removed entry.beforeView,
    Command.erase app removed entry.command⟩

end ReactiveApplication

end Interaction
