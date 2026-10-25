/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Foundation.Context

/-! # Collecting selected positions of typed partial environments -/

noncomputable section

namespace Vegas

namespace PartialEnvironment

variable {Ty : Type} {Val : Ty → Type}
  (selected : VarId → Ty → Prop) [∀ name ty, Decidable (selected name ty)]

/-- Collect exactly the selected typed positions. Selection may depend on both
the variable name and its type; repeated names need not identify positions. -/
def collect? : (schema : Ctx Ty) →
    (∀ {name ty}, HasVar schema name ty → selected name ty → Option (Val ty)) →
    Option (∀ {name ty}, HasVar schema name ty → selected name ty → Val ty)
  | [], _ => some fun ref _ => nomatch ref
  | (name, ty) :: tail, lookup => do
      let tailGet ← collect? tail (fun ref used => lookup (.there ref) used)
      if used : selected name ty then
        let head ← lookup (HasVar.here : HasVar ((name, ty) :: tail) name ty) used
        pure fun {_ _} ref read => match ref with
          | .here => head
          | .there ref => tailGet ref read
      else
        pure fun {_ _} ref read => match ref with
          | .here => False.elim (used read)
          | .there ref => tailGet ref read

theorem congr (schema : Ctx Ty)
    (left right : ∀ {name ty}, HasVar schema name ty → selected name ty → Option (Val ty))
    (agree : ∀ {name ty} (ref : HasVar schema name ty) (read : selected name ty),
      left ref read = right ref read) :
    collect? selected schema left = collect? selected schema right := by
  apply congrArg (collect? selected schema)
  funext name ty ref read
  exact agree ref read

theorem of_some (schema : Ctx Ty)
    (lookup : ∀ {name ty}, HasVar schema name ty → selected name ty → Option (Val ty))
    (values : ∀ {name ty}, HasVar schema name ty → selected name ty → Val ty)
    (agree : ∀ {name ty} (ref : HasVar schema name ty) (read : selected name ty),
      lookup ref read = some (values ref read)) :
    collect? selected schema lookup =
      (some values : Option (∀ {name ty}, HasVar schema name ty → selected name ty → Val ty)) := by
  induction schema with
  | nil =>
      apply congrArg some
      funext name ty ref
      nomatch ref
  | cons entry tail ih =>
      obtain ⟨name, ty⟩ := entry
      have tailCollected := ih (fun ref read => lookup (.there ref) read)
        (fun ref read => values (.there ref) read) (fun ref read => agree (.there ref) read)
      by_cases used : selected name ty
      · simp only [collect?, tailCollected, dite_eq_left used, agree HasVar.here used]
        apply congrArg some
        funext readName readTy ref read
        cases ref <;> rfl
      · simp only [collect?, tailCollected, dite_eq_right used]
        apply congrArg some
        funext readName readTy ref read
        cases ref with
        | here => exact absurd read used
        | there ref => rfl

theorem lookup_of_some (schema : Ctx Ty)
    (lookup : ∀ {name ty}, HasVar schema name ty → selected name ty → Option (Val ty))
    (values : ∀ {name ty}, HasVar schema name ty → selected name ty → Val ty)
    (collected : collect? selected schema lookup =
      (some values : Option (∀ {name ty}, HasVar schema name ty → selected name ty → Val ty)))
    {name ty} (ref : HasVar schema name ty) (read : selected name ty) :
    lookup ref read = some (values ref read) := by
  induction schema with
  | nil => nomatch ref
  | cons entry tail ih =>
      obtain ⟨headName, headTy⟩ := entry
      cases tailCollected : collect? selected tail
          (fun ref read => lookup (.there ref) read) with
      | none => simp [collect?, tailCollected] at collected
      | some tailGet =>
          by_cases used : selected headName headTy
          · cases headCollected : lookup
                (HasVar.here : HasVar ((headName, headTy) :: tail) headName headTy) used with
            | none =>
                simp [collect?, tailCollected, used, headCollected] at collected
            | some head =>
                simp only [collect?, tailCollected, dite_eq_left used, headCollected] at collected
                have equal := Option.some.inj collected
                have point := congrArg
                  (fun get : ∀ {name ty}, HasVar ((headName, headTy) :: tail) name ty →
                    selected name ty → Val ty => get ref read) equal
                rw [← point]
                cases ref with
                | here => exact headCollected
                | there ref => exact ih _ _ tailCollected ref
          · simp only [collect?, tailCollected, dite_eq_right used] at collected
            have equal := Option.some.inj collected
            have point := congrArg
              (fun get : ∀ {name ty}, HasVar ((headName, headTy) :: tail) name ty →
                selected name ty → Val ty => get ref read) equal
            rw [← point]
            cases ref with
            | here => exact False.elim (used read)
            | there ref => exact ih _ _ tailCollected ref

theorem eq_some_iff (schema : Ctx Ty)
    (lookup : ∀ {name ty}, HasVar schema name ty → selected name ty → Option (Val ty))
    (values : ∀ {name ty}, HasVar schema name ty → selected name ty → Val ty) :
    collect? selected schema lookup =
      (some values : Option (∀ {name ty}, HasVar schema name ty → selected name ty → Val ty)) ↔
      ∀ {name ty} (ref : HasVar schema name ty) (read : selected name ty),
        lookup ref read = some (values ref read) :=
  ⟨fun collected _ _ ref read => lookup_of_some selected schema lookup values collected ref read,
    of_some selected schema lookup values⟩

theorem isSome_iff (schema : Ctx Ty)
    (lookup : ∀ {name ty}, HasVar schema name ty → selected name ty → Option (Val ty)) :
    (collect? selected schema lookup).isSome = true ↔
      ∀ {name ty} (ref : HasVar schema name ty) (read : selected name ty),
        (lookup ref read).isSome = true := by
  constructor
  · intro present
    obtain ⟨values, collected⟩ := Option.isSome_iff_exists.mp present
    intro name ty ref read
    rw [lookup_of_some selected schema lookup values collected ref read]
    rfl
  · intro available
    classical
    let values : ∀ {name ty}, HasVar schema name ty → selected name ty → Val ty :=
      fun ref read => Classical.choose (Option.isSome_iff_exists.mp (available ref read))
    have collected := of_some selected schema lookup values
      (fun ref read => Classical.choose_spec (Option.isSome_iff_exists.mp (available ref read)))
    rw [collected]
    rfl

theorem eq_none_of_lookup_none (schema : Ctx Ty)
    (lookup : ∀ {name ty}, HasVar schema name ty → selected name ty → Option (Val ty))
    {name ty} (ref : HasVar schema name ty) (read : selected name ty)
    (failed : lookup ref read = none) : collect? selected schema lookup = none := by
  cases collected : collect? selected schema lookup with
  | none => rfl
  | some values =>
      have found := lookup_of_some selected schema lookup values collected ref read
      rw [failed] at found
      cases found

end PartialEnvironment

end Vegas
