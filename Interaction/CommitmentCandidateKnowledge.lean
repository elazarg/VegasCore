/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidates

/-! # Agreement on disclosed candidate meanings

Preparation and acceptance preserve agreement on designated handles. Hidden
handles need not even have the same openability or freshness: neither operation
returns a public test of their contents. Authentication and the admissible
opening queries are obligations of the hosting protocol.
-/

namespace Interaction.CommitmentCandidates

universe uPrincipal uSlot uValue

variable {Principal : Type uPrincipal} {Slot : Type uSlot} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Slot]
variable {left right : CommitmentCandidates Principal Slot Value}
variable {known : CommitmentHandle Principal Slot → Prop}

theorem prepare_lookup_eq_of_known
    (hagrees : ∀ handle, known handle → left.lookup handle = right.lookup handle)
    (owner : Principal) (slot : Slot) (leftValue rightValue : Value)
    (hvalue : known (owner, slot) → leftValue = rightValue)
    (handle : CommitmentHandle Principal Slot) (hknown : known handle) :
    (left.prepare owner slot leftValue).lookup handle =
      (right.prepare owner slot rightValue).lookup handle := by
  by_cases heq : handle = (owner, slot)
  · subst handle
    rw [lookup_prepare_self, lookup_prepare_self, hagrees _ hknown, hvalue hknown]
  · rw [left.lookup_prepare_other owner slot leftValue handle heq,
      right.lookup_prepare_other owner slot rightValue handle heq]
    exact hagrees handle hknown

theorem accept_lookup_eq_of_known
    (hagrees : ∀ handle, known handle → left.lookup handle = right.lookup handle)
    (accepted handle : CommitmentHandle Principal Slot) (hknown : known handle) :
    (left.accept accepted).lookup handle = (right.accept accepted).lookup handle := by
  by_cases heq : handle = accepted
  · subst handle
    rw [lookup_accept_self, lookup_accept_self, hagrees _ hknown]
  · rw [left.lookup_accept_other accepted handle heq, right.lookup_accept_other accepted handle heq]
    exact hagrees handle hknown

end Interaction.CommitmentCandidates
