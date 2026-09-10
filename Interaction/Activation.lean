/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

/-! # Public activation clocks

A runtime records when a named obligation becomes active. Administrative
steps retain the origin; changing the active obligation records a new origin.
This component neither schedules work nor resolves overdue obligations.
-/

namespace Interaction

universe u

/-- An active obligation and the public clock at which it became active. -/
structure Activation (Key : Type u) where
  key : Key
  since : Nat
  deriving DecidableEq, Repr

namespace Activation

variable {Key : Type u}

/-- Preserve an unchanged obligation's origin; record the supplied public
clock when the active key changes. No active key means no running window. -/
def refresh [DecidableEq Key] (prior : Option (Activation Key))
    (key : Option Key) (clock : Nat) : Option (Activation Key) :=
  if prior.map Activation.key = key then prior else key.map (⟨·, clock⟩)

@[simp] theorem refresh_key [DecidableEq Key]
    (prior : Option (Activation Key)) (key : Option Key) (clock : Nat) :
    (refresh prior key clock).map Activation.key = key := by
  unfold refresh
  split
  · assumption
  · cases key <;> rfl

theorem refresh_unchanged [DecidableEq Key]
    (prior : Option (Activation Key)) (key : Option Key) (clock : Nat)
    (hsame : prior.map Activation.key = key) : refresh prior key clock = prior := by
  simp [refresh, hsame]

theorem refresh_changed [DecidableEq Key]
    (prior : Option (Activation Key)) (key : Option Key) (clock : Nat)
    (hchanged : prior.map Activation.key ≠ key) :
    refresh prior key clock = key.map (⟨·, clock⟩) := by
  simp [refresh, hchanged]

/-- Refreshing cannot put an origin in the future if retained origins are
already bounded by the current public clock. -/
theorem refresh_since_le [DecidableEq Key]
    (prior : Option (Activation Key)) (key : Option Key) (clock : Nat)
    (hpast : ∀ activation ∈ prior, activation.since ≤ clock) :
    ∀ activation ∈ refresh prior key clock, activation.since ≤ clock := by
  unfold refresh
  split
  · exact hpast
  · cases key with
    | none => simp
    | some key => simp

/-- The absolute boundary of a duration measured from this activation. -/
def deadline (activation : Activation Key) (window : Nat) : Nat := activation.since + window

theorem not_overdue_at_activation (activation : Activation Key) (window : Nat) :
    ¬activation.deadline window < activation.since :=
  Nat.not_lt_of_ge (Nat.le_add_right _ _)

end Activation

end Interaction
