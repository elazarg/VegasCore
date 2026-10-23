/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

/-! # Ideal write-once commitments

This is a model study, not the mechanism its users end up with: the Vegas host
builds its own application, hiding a binding inside that application's public
projection, and no capstone of theirs reaches this module. It is kept as a reference functionality and is
exercised by its own regressions.

This is an ideal hidden write-once functionality with a private registration
interface. A handle contains only an owner and slot, independently of the
registered value. Opening messages carry a claimed value. An operational
adapter must authenticate the opening before checking it against the private
table; exposing the check as an unrestricted oracle would disclose guesses'
correctness before opening.

The first authenticated registration at an owner/slot pair permanently fixes
the sole value for that handle. This is stronger than a bare hiding-and-binding
interface: the functionality does not represent multiple candidate commitments
for one slot, and applications can require registration before accepting the
handle. Refining a protocol that admits competing candidates or accepts an
unopenable candidate requires a strategic argument, not only a codec between
representations.

This model is not software cryptography or deployable public storage. It gives
no liveness, forced-opening, delivery, or release-barrier guarantee.
Its table and verification functions are specification operations. This file
does not define a strategy interface: hiding requires a separate interface
that does not hand these operations or the table to an opponent.
-/

namespace Interaction

universe uPrincipal uSlot uValue

/-- The canonical handle for an owner-scoped registration slot. Applications
may identify the slot with a source site. -/
abbrev CommitmentHandle (Principal : Type uPrincipal) (Slot : Type uSlot) :=
  Principal × Slot

/-- Private ideal storage, indexed by authenticated owner and slot. -/
structure IdealCommitments (Principal : Type uPrincipal) (Slot : Type uSlot)
    (Value : Type uValue) where
  table : Principal → Slot → Option Value

namespace IdealCommitments

variable {Principal : Type uPrincipal} {Slot : Type uSlot} {Value : Type uValue}

/-- The initially empty functionality. -/
def empty : IdealCommitments Principal Slot Value where
  table := fun _ _ => none

/-- Read ideal storage for specification and proof. This is not a public
runtime operation. -/
def lookup (state : IdealCommitments Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) : Option Value :=
  state.table handle.1 handle.2

/-- The result of a private authenticated seal request. -/
structure SealResult where
  accepted : Bool
  state : IdealCommitments Principal Slot Value

/-- Privately register the first and only value at an authenticated
owner-scoped slot. Later registrations are rejected without changing it. -/
def sealValue (state : IdealCommitments Principal Slot Value)
    [DecidableEq Principal] [DecidableEq Slot]
    (owner : Principal) (slot : Slot) (value : Value) :
    SealResult (Principal := Principal) (Slot := Slot) (Value := Value) :=
  match state.table owner slot with
  | some _ => ⟨false, state⟩
  | none =>
      ⟨true, { table := fun otherOwner otherSlot =>
        if otherOwner = owner ∧ otherSlot = slot then some value
        else state.table otherOwner otherSlot }⟩

/-- A public opening message carries its claimed value. -/
structure Opening where
  handle : CommitmentHandle Principal Slot
  claimed : Value

/-- The ideal service's private-table check for a claimed opening. It does not
authenticate a sender and must only be invoked after an application has checked
the opening message's sender and expected owner/slot. Exposing this Boolean as
an unrestricted pre-opening query oracle would violate the intended hiding. -/
def verify (state : IdealCommitments Principal Slot Value)
    [DecidableEq Value]
    (opening : Opening (Principal := Principal) (Slot := Slot) (Value := Value)) : Bool :=
  state.lookup opening.handle == some opening.claimed

@[simp] theorem lookup_empty (handle : CommitmentHandle Principal Slot) :
    (empty : IdealCommitments Principal Slot Value).lookup handle = none := rfl

/-- A claim is accepted exactly when that claimed value is stored at its
owner-scoped handle. -/
theorem verify_eq_true_iff (state : IdealCommitments Principal Slot Value)
    [DecidableEq Value]
    (opening : Opening (Principal := Principal) (Slot := Slot) (Value := Value)) :
    state.verify opening = true ↔
      state.lookup opening.handle = some opening.claimed := by
  simp [verify]

end IdealCommitments

end Interaction
