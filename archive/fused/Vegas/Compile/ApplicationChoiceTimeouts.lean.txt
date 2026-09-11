/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage
import Vegas.Compile.ApplicationBindingOrigins

/-! # Optional timeout code in the public-message artifact

Timeout decoration changes only the optional resolution code of public-choice
instructions. Addresses, source guards, fields, prerequisite lists, and all
other instructions are retained. The result uses the same message alphabet,
state carrier, observations, and shared interpreter.

The selection function is a compiler input, not an interpreter callback: its
result is a finite image containing typed expression code. Source legality and
availability of a selected expression are separate compiler obligations. The
handler still validates its result before publishing it.
-/

namespace Vegas

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} {L : IExpr}

namespace ApplicationInstruction

/-- Replace optional timeout metadata without changing the instruction's
ordinary execution path. -/
def withChoiceTimeouts
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)) :
    ApplicationInstruction P L → ApplicationInstruction P L
  | .publicChoice code => .publicChoice { code with timeout := select code }
  | .sample code => .sample code
  | .bind code => .bind code
  | .conditional code => .conditional code

@[simp] theorem withChoiceTimeouts_address
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (instruction : ApplicationInstruction P L) :
    (instruction.withChoiceTimeouts select).address = instruction.address := by
  cases instruction <;> rfl

end ApplicationInstruction

namespace ApplicationImage

/-- A finite compiler pass that attaches public-choice resolution code. -/
def withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)) :
    ApplicationImage P L :=
  ⟨image.instructions.map (ApplicationInstruction.withChoiceTimeouts select)⟩

@[simp] theorem lookup_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (address : Nat) :
    (image.withChoiceTimeouts select).lookup address =
      (image.lookup address).map (ApplicationInstruction.withChoiceTimeouts select) := by
  simp [lookup, withChoiceTimeouts, List.find?_map]

/-- Chance behavior is unchanged by public-choice timeout metadata. -/
theorem sample_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (state : State P L) (address : Nat) :
    (image.withChoiceTimeouts select).sample state address = image.sample state address := by
  simp only [sample, lookup_withChoiceTimeouts]
  cases image.lookup address with
  | none => rfl
  | some instruction => cases instruction <;> rfl

/-- Traffic outside the newly enabled expiry entry point. This predicate is
used only for a conservativity theorem, never to restrict the runtime alphabet. -/
def Payload.NotChoiceExpiry : Payload P L → Prop
  | .expireChoice _ => False
  | _ => True

/-- Ordinary submissions, including malformed traffic, execute identically.
Expiry requests remain a genuine additional opportunity in the decorated image. -/
theorem handle_withChoiceTimeouts [DecidableEq P] (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (state : State P L) (message : Message P (Payload P L))
    (hordinary : message.payload.NotChoiceExpiry) :
    (image.withChoiceTimeouts select).handle state message = image.handle state message := by
  obtain ⟨id, payload⟩ := message
  cases payload with
  | expireChoice address => exact False.elim hordinary
  | malformed data => rfl
  | choice address typed =>
      simp only [handle, lookup_withChoiceTimeouts]
      cases image.lookup address with
      | none => rfl
      | some instruction => cases instruction <;> rfl
  | binding address commitment =>
      simp only [handle, lookup_withChoiceTimeouts]
      cases image.lookup address with
      | none => rfl
      | some instruction => cases instruction <;> rfl
  | expireBinding address =>
      simp only [handle, lookup_withChoiceTimeouts]
      cases image.lookup address with
      | none => rfl
      | some instruction => cases instruction <;> rfl
  | conditional address payload =>
      simp only [handle, lookup_withChoiceTimeouts]
      cases image.lookup address with
      | none => rfl
      | some instruction => cases instruction <;> rfl

/-- An accepted timeout has the same application-state effect as some accepted
ordinary packet at the original image. The witness is proof data; no message is
forged, enqueued, or attributed to an owner in the actual execution. This local
state comparison is not a strategy backtranslation. -/
theorem handle_withChoiceTimeouts_source [DecidableEq P] (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (state : State P L) (message : Message P (Payload P L)) (next : State P L)
    (hnext : (image.withChoiceTimeouts select).handle state message = some next) :
    ∃ original : Message P (Payload P L), image.handle state original = some next := by
  by_cases hordinary : message.payload.NotChoiceExpiry
  · exact ⟨message, (image.handle_withChoiceTimeouts select state message hordinary).symm.trans
      hnext⟩
  obtain ⟨id, payload⟩ := message
  cases payload with
  | choice address typed | binding address commitment | expireBinding address
  | conditional address payload
  | malformed data => exact False.elim (hordinary trivial)
  | expireChoice address =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hnext
      | some instruction =>
          cases instruction with
          | sample code | bind code | conditional code =>
              simp [handle, hlookup, ApplicationInstruction.withChoiceTimeouts] at hnext
          | publicChoice code =>
              let timed : PublicChoiceCode P L := { code with timeout := select code }
              have htimed : (image.withChoiceTimeouts select).lookup address =
                  some (.publicChoice timed) := by simp [hlookup, timed,
                    ApplicationInstruction.withChoiceTimeouts]
              rw [(image.withChoiceTimeouts select).handle_expireChoice
                state address timed htimed id] at hnext
              obtain ⟨value, hresolved, rfl⟩ := Option.map_eq_some_iff.mp hnext
              have hvalid := timed.resolveTimeout?_some state.memory value hresolved
              refine ⟨⟨(code.endpoint.owner, 0), .choice address ⟨code.guard.ty, value⟩⟩, ?_⟩
              rw [image.handle_choice state address code hlookup _ value]
              have hresolve : code.endpoint.resolve? state.memory.done
                  (code.guard.validate state.memory.store) ⟨(code.endpoint.owner, 0), value⟩ =
                  some value :=
                (code.endpoint.resolve_iff _ _ _ _).mpr ⟨hvalid.1, rfl, hvalid.2, rfl⟩
              rw [hresolve, Option.map_some]
              rfl

private theorem originsFrom_withChoiceTimeouts
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (earlier : List (BindingCode P L))
    (instructions : List (ApplicationInstruction P L))
    (horigins : HasBindingOriginsFrom earlier instructions) :
    HasBindingOriginsFrom earlier
      (instructions.map (ApplicationInstruction.withChoiceTimeouts select)) := by
  induction instructions generalizing earlier with
  | nil => trivial
  | cons instruction rest ih =>
      cases instruction with
      | sample code => exact ih earlier horigins
      | publicChoice code => exact ih earlier horigins
      | bind code => exact ih (code :: earlier) horigins
      | conditional code => exact ⟨horigins.1, ih earlier horigins.2⟩

/-- Adding optional public-choice fallback code preserves every static
conditional binding origin. -/
theorem HasBindingOrigins.withChoiceTimeouts
    {image : ApplicationImage P L} (horigins : image.HasBindingOrigins)
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)) :
    (image.withChoiceTimeouts select).HasBindingOrigins := by
  exact originsFrom_withChoiceTimeouts select [] image.instructions horigins

end ApplicationImage

end Vegas
