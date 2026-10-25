/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Foundation.PartialEnvironment

/-! # Typed selection and missing cells in partial environments -/

namespace VegasTests.PartialEnvironment

open Vegas

inductive Cell where
  | flag
  | count
  deriving DecidableEq

def Value : Cell → Type
  | .flag => Bool
  | .count => Nat

def countsAtZero (name : VarId) (cell : Cell) : Prop := name = 0 ∧ cell = .count

instance (name : VarId) (cell : Cell) : Decidable (countsAtZero name cell) :=
  inferInstanceAs (Decidable (name = 0 ∧ cell = .count))

def mixed : Ctx Cell := [(0, .flag), (0, .count), (1, .count)]

def mixedLookup : {name : VarId} → {cell : Cell} →
    HasVar mixed name cell → Option (Value cell)
  | _, _, .here => none
  | _, _, .there .here => some (7 : Nat)
  | _, _, .there (.there .here) => none
  | _, _, .there (.there (.there ref)) => nomatch ref

/-- A missing flag at the same name, and an irrelevant missing count, do not
block the selected count. Selection distinguishes the two types at name zero. -/
theorem irrelevant_missing_positions :
    (PartialEnvironment.collect? countsAtZero mixed (fun ref _ => mixedLookup ref)).map
      (fun get => get (.there .here) ⟨rfl, rfl⟩) = some (7 : Nat) := by
  rfl

/-- The same lookup fails when the missing flag is selected as well. -/
theorem selected_missing_position :
    PartialEnvironment.collect? (fun name (_ : Cell) => name = 0) mixed
      (fun ref _ => mixedLookup ref) = none := by
  rfl

def repeated : Ctx Cell := [(0, .count), (0, .count)]

def repeatedLookup : {name : VarId} → {cell : Cell} →
    HasVar repeated name cell → Option (Value cell)
  | _, _, .here => some (7 : Nat)
  | _, _, .there .here => some (9 : Nat)
  | _, _, .there (.there ref) => nomatch ref

/-- Even equal names and equal types retain distinct context positions. No
unique-name premise or canonicalized variable lookup is involved. -/
theorem repeated_names_retain_positions :
    (PartialEnvironment.collect? countsAtZero repeated (fun ref _ => repeatedLookup ref)).map
      (fun get => (get .here ⟨rfl, rfl⟩, get (.there .here) ⟨rfl, rfl⟩)) =
        some ((7 : Nat), (9 : Nat)) := by
  rfl

end VegasTests.PartialEnvironment
