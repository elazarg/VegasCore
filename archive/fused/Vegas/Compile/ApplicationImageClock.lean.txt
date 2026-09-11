/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationImageSamples

/-! # Clock preservation for application-image transitions

Message handling and chance sampling do not advance the public clock. Ordered
admission retains those equations; its environment transition is monotone
because an explicit clock advance takes a maximum and every other branch
either samples or stutters.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every successful application-image handler preserves the public clock. -/
theorem handle_clock (image : ApplicationImage P L) (before after : State P L)
    (message : Message P (Payload P L)) (hafter : image.handle before message = some after) :
    after.memory.clock = before.memory.clock := by
  rcases message with ⟨id, payload⟩
  cases payload with
  | malformed data => simp [handle] at hafter
  | choice address typed =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          cases instruction with
          | sample code | bind code | conditional code => simp [handle, hlookup] at hafter
          | publicChoice code =>
              simp only [handle, hlookup, Option.bind_eq_bind, Option.bind_some] at hafter
              cases htyped : typed.as? code.guard.ty with
              | none => simp [htyped] at hafter
              | some value =>
                  simp only [htyped, Option.bind_some] at hafter
                  cases hresolved : code.endpoint.resolve? before.memory.done
                      (code.guard.validate before.memory.store) ⟨id, value⟩ with
                  | none => simp [hresolved] at hafter
                  | some accepted =>
                      simp only [hresolved, Option.bind_some] at hafter
                      cases hafter
                      rfl
  | expireChoice address =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          cases instruction with
          | sample code | bind code | conditional code => simp [handle, hlookup] at hafter
          | publicChoice code =>
              rw [image.handle_expireChoice before address code hlookup id] at hafter
              obtain ⟨value, _, rfl⟩ := Option.map_eq_some_iff.mp hafter
              rfl
  | binding address bindingHandle =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          cases instruction with
          | sample code | publicChoice code | conditional code => simp [handle, hlookup] at hafter
          | bind code =>
              simp only [handle, hlookup, Option.bind_eq_bind, Option.bind_some] at hafter
              split at hafter
              · cases hafter
                rfl
              · contradiction
  | expireBinding address =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          cases instruction with
          | sample code | publicChoice code | conditional code => simp [handle, hlookup] at hafter
          | bind code =>
              rw [image.handle_expireBinding before address code hlookup id] at hafter
              obtain ⟨value, _, rfl⟩ := Option.map_eq_some_iff.mp hafter
              rfl
  | conditional address request =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          cases instruction with
          | sample code | publicChoice code | bind code => simp [handle, hlookup] at hafter
          | conditional code =>
              simp only [handle, hlookup, Option.bind_eq_bind, Option.bind_some] at hafter
              cases hdecoded : code.decode request with
              | none => simp [hdecoded] at hafter
              | some decoded =>
                  simp only [hdecoded, Option.bind_some] at hafter
                  cases hresolved : code.endpoint.resolveDisposition? before.memory.clock
                      (before.verify code) (code.binding? before.memory) before.memory.done
                      (code.canOpen before.memory.store) ⟨id, decoded⟩ with
                  | none => simp [hresolved] at hafter
                  | some result =>
                      simp only [hresolved, Option.bind_some] at hafter
                      cases hafter
                      rfl

omit [DecidableEq P] in
/-- Every supported chance transition preserves the public clock, including
the stutter branches for missing, completed, unready, or unreadable code. -/
theorem sample_clock (image : ApplicationImage P L) (before after : State P L)
    (address : Nat) (hafter : after ∈ (image.sample before address).support) :
    after.memory.clock = before.memory.clock := by
  rcases image.sample_support before address after hafter with rfl | hsample
  · rfl
  · obtain ⟨code, reads, value, _, _, _, _, _, rfl⟩ := hsample
    rfl

/-- A successful handler call through ordered admission has the same clock
equation as its underlying application-image handler. -/
theorem ordered_handle_clock (image : ApplicationImage P L) (before after : State P L)
    (message : Message P (Payload P L))
    (hafter : image.orderedApplication.handle before message = some after) :
    after.memory.clock = before.memory.clock := by
  change (image.application.withAdmission image.admitsMessage
    image.admitsEnvironment).handle before message = some after at hafter
  exact image.handle_clock before after message <|
    image.application.withAdmission_handle_some image.admitsMessage
      image.admitsEnvironment before after message hafter

/-- Ordered environment transitions never decrease the public clock. Sampling
preserves it, a disabled command stutters, and advance takes a maximum. -/
theorem ordered_environmentStep_clock_mono (image : ApplicationImage P L)
    (before after : State P L) (command : EnvironmentCommand)
    (hafter : after ∈
      (image.orderedApplication.environmentStep before command).support) :
    before.memory.clock ≤ after.memory.clock := by
  cases command with
  | advance clock =>
      rw [image.ordered_advance] at hafter
      simp only [FinDist.mem_support_pure] at hafter
      subst after
      exact Nat.le_max_left _ _
  | sample address =>
      change after ∈ ((image.application.withAdmission image.admitsMessage
        image.admitsEnvironment).environmentStep before (.sample address)).support at hafter
      rcases image.application.withAdmission_environment_support image.admitsMessage
        image.admitsEnvironment before after (.sample address) hafter with rfl | hsample
      · exact Nat.le_refl _
      · exact Nat.le_of_eq (image.sample_clock before after address hsample).symm

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.handle_clock' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.handle_clock

/-- info: 'Vegas.ApplicationImage.sample_clock' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.sample_clock

/-- info: 'Vegas.ApplicationImage.ordered_handle_clock' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_handle_clock

/-- info: 'Vegas.ApplicationImage.ordered_environmentStep_clock_mono' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_environmentStep_clock_mono
