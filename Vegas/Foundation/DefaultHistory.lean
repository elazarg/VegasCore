/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Data.Finset.Image

/-! # Public default history

Each completed instruction contributes one public entry, newest first.
`some player` records a newly public default; `none` records completion without
a new default. Keeping the entries preserves when a default was observed.
The current default set is derived from this record.
-/

namespace Vegas

/-- Public default events, indexed by their position among completed instructions. -/
structure DefaultHistory (Player : Type) where
  events : List (Option Player)
deriving DecidableEq

namespace DefaultHistory

variable {Player : Type} [DecidableEq Player]

/-- Players whose default has become public. -/
def defaulted (history : DefaultHistory Player) : Finset Player :=
  (history.events.filterMap id).toFinset

/-- Complete one instruction, retaining its public default event if any. -/
def record (history : DefaultHistory Player) (event : Option Player) : DefaultHistory Player :=
  ⟨event :: history.events⟩

/-- The public record before the most recently completed instruction. -/
def back (history : DefaultHistory Player) : DefaultHistory Player := ⟨history.events.tail⟩

omit [DecidableEq Player] in
@[simp] theorem back_record (history : DefaultHistory Player) (event : Option Player) :
    (history.record event).back = history := by cases history; rfl

@[simp] theorem defaulted_record_none (history : DefaultHistory Player) :
    (history.record none).defaulted = history.defaulted := rfl

@[simp] theorem defaulted_record_some (history : DefaultHistory Player) (who : Player) :
    (history.record (some who)).defaulted = insert who history.defaulted := by
  simp [defaulted, record]

/-- Completing another instruction never removes a public default. -/
theorem defaulted_mono (history : DefaultHistory Player) (event : Option Player) :
    history.defaulted ⊆ (history.record event).defaulted := by
  cases event with
  | none => exact Finset.Subset.refl _
  | some who => simpa only [defaulted_record_some] using Finset.subset_insert who history.defaulted

end DefaultHistory

end Vegas
