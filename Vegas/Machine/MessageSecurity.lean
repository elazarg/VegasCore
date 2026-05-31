/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Basic

/-!
# Message-buffer plaintext predicates

Small reusable predicates for stating when a public message buffer contains
action-relevant plaintext.  Runtime examples instantiate `PlaintextPolicy` for
their own message type; the generic invariant is just that the extracted
plaintext list is empty at the relevant lock point.
-/

namespace Vegas

namespace Machine

structure PlaintextPolicy
    (Player : Type) (Message : Player → Type) (Plaintext : Type) where
  plaintext? : ∀ player, Message player → Option Plaintext

namespace PlaintextPolicy

variable {Player Plaintext : Type} {Message : Player → Type}

def plaintexts
    (policy : PlaintextPolicy Player Message Plaintext) :
    List (Sigma Message) → List (Player × Plaintext)
  | [] => []
  | ⟨player, message⟩ :: rest =>
      match policy.plaintext? player message with
      | none => policy.plaintexts rest
      | some plaintext => (player, plaintext) :: policy.plaintexts rest

def noPlaintext
    (policy : PlaintextPolicy Player Message Plaintext)
    (messages : List (Sigma Message)) : Prop :=
  policy.plaintexts messages = []

@[simp] theorem plaintexts_nil
    (policy : PlaintextPolicy Player Message Plaintext) :
    policy.plaintexts [] = [] := rfl

@[simp] theorem noPlaintext_nil
    (policy : PlaintextPolicy Player Message Plaintext) :
    policy.noPlaintext [] := rfl

theorem plaintexts_append
    (policy : PlaintextPolicy Player Message Plaintext)
    (left right : List (Sigma Message)) :
    policy.plaintexts (left ++ right) =
      policy.plaintexts left ++ policy.plaintexts right := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨player, message⟩
      cases h : policy.plaintext? player message <;>
        simp [plaintexts, h, ih]

end PlaintextPolicy

end Machine
end Vegas
