/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Int.Basic

/-! # Aggregating integer transfer instructions

Summing executable transfers does not depend on utility, valuation or auditing.
-/

namespace GameTheory

/-- Sum all transfer entries belonging to a player, including duplicates. -/
def transferAmount {Player : Type*} [DecidableEq Player]
    (entries : List (Player × Int)) (who : Player) : Int :=
  (entries.map fun entry => if entry.1 = who then entry.2 else 0).sum

@[simp] theorem transferAmount_nil {Player : Type*} [DecidableEq Player] (who : Player) :
    transferAmount ([] : List (Player × Int)) who = 0 := rfl

@[simp] theorem transferAmount_cons {Player : Type*} [DecidableEq Player]
    (entry : Player × Int) (entries : List (Player × Int)) (who : Player) :
    transferAmount (entry :: entries) who =
      (if entry.1 = who then entry.2 else 0) + transferAmount entries who := rfl

/-- Appending transfer instructions adds their monetary effects. -/
theorem transferAmount_append {Player : Type*} [DecidableEq Player]
    (first second : List (Player × Int)) (who : Player) :
    transferAmount (first ++ second) who =
      transferAmount first who + transferAmount second who := by
  simp only [transferAmount, List.map_append, List.sum_append]

end GameTheory
