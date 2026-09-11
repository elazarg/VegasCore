/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationDeadlines
import Vegas.Compile.ApplicationOrder

/-! # Deadline-independent application traffic

Replacing application deadlines changes only the three explicit expiry entry
points. Ordinary bindings and choices, voluntary conditional publication,
malformed traffic, and their ordered admission behavior remain unchanged.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Payload

/-- Traffic whose handler semantics does not inspect an instruction deadline.
Conditional decline is voluntary and therefore remains deadline-independent. -/
def DeadlineIndependent : ApplicationImage.Payload P L → Prop
  | .expireChoice _ | .expireBinding _ | .conditional _ .expire => False
  | _ => True

end Payload

private theorem conditional_handle_withDeadline_eq
    (code : ConditionalCode P L) (deadline : Nat) (state : State P L)
    (id : MessageId P) (request : ConditionalPublication.Payload P (TypedValue L))
    (hindependent : match request with | .expire => False | _ => True) :
    (let retimed : ConditionalCode P L :=
        { code with endpoint := { code.endpoint with deadline } };
      do
        let decoded ← retimed.decode request
        let result ← retimed.endpoint.resolveDisposition? state.memory.clock
          (state.verify retimed) (retimed.binding? state.memory) state.memory.done
          (retimed.canOpen state.memory.store) ⟨id, decoded⟩
        pure (state.publishConditional retimed result)) =
      (do
        let decoded ← code.decode request
        let result ← code.endpoint.resolveDisposition? state.memory.clock
          (state.verify code) (code.binding? state.memory) state.memory.done
          (code.canOpen state.memory.store) ⟨id, decoded⟩
        pure (state.publishConditional code result)) := by
  let retimed : ConditionalCode P L :=
    { code with endpoint := { code.endpoint with deadline } }
  have hverify : state.verify retimed = state.verify code := rfl
  have hbinding : retimed.binding? state.memory = code.binding? state.memory := rfl
  have hcanOpen : retimed.canOpen state.memory.store = code.canOpen state.memory.store := rfl
  have hdecode : retimed.decode request = code.decode request := rfl
  have hendpoint : retimed.endpoint = { code.endpoint with deadline } := rfl
  have hpublish : ∀ result, state.publishConditional retimed result =
      state.publishConditional code result := by
    intro result
    rfl
  change (do
      let decoded ← retimed.decode request
      let result ← retimed.endpoint.resolveDisposition? state.memory.clock
        (state.verify retimed) (retimed.binding? state.memory) state.memory.done
        (retimed.canOpen state.memory.store) ⟨id, decoded⟩
      pure (state.publishConditional retimed result)) = _
  rw [hverify, hbinding, hcanOpen, hdecode, hendpoint]
  cases request with
  | expire => exact False.elim hindependent
  | malformed => rfl
  | decline =>
      simp only [ConditionalCode.decode, Option.bind_eq_bind, Option.bind_some]
      rw [ConditionalPublication.resolveDisposition_withDeadline_eq
        (deadline := deadline) (hindependent := by trivial)]
      cases code.endpoint.resolveDisposition? state.memory.clock (state.verify code)
          (code.binding? state.memory) state.memory.done (code.canOpen state.memory.store)
          ⟨id, .decline⟩ <;> simp [hpublish]
  | opening handle typed =>
      cases htyped : typed.as? code.secretTy with
      | none => simp [ConditionalCode.decode, htyped]
      | some value =>
          simp only [ConditionalCode.decode, htyped, Option.map_some,
            Option.bind_eq_bind, Option.bind_some]
          rw [ConditionalPublication.resolveDisposition_withDeadline_eq
            (deadline := deadline) (hindependent := by trivial)]
          cases code.endpoint.resolveDisposition? state.memory.clock (state.verify code)
              (code.binding? state.memory) state.memory.done (code.canOpen state.memory.store)
              ⟨id, .opening handle value⟩ <;> simp [hpublish]
  | cleartext typed =>
      cases htyped : typed.as? code.secretTy with
      | none => simp [ConditionalCode.decode, htyped]
      | some value =>
          simp only [ConditionalCode.decode, htyped, Option.map_some,
            Option.bind_eq_bind, Option.bind_some]
          rw [ConditionalPublication.resolveDisposition_withDeadline_eq
            (deadline := deadline) (hindependent := by trivial)]
          cases code.endpoint.resolveDisposition? state.memory.clock (state.verify code)
              (code.binding? state.memory) state.memory.done (code.canOpen state.memory.store)
              ⟨id, .cleartext value⟩ <;> simp [hpublish]

/-- Retiming an image leaves every non-expiry handler call exactly unchanged. -/
theorem handle_withDeadlines_eq (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (state : State P L) (message : Message P (Payload P L))
    (hindependent : message.payload.DeadlineIndependent) :
    (image.withDeadlines deadlineOf).handle state message = image.handle state message := by
  obtain ⟨id, payload⟩ := message
  cases payload with
  | expireChoice address | expireBinding address => exact False.elim hindependent
  | malformed data => rfl
  | choice address typed =>
      simp only [ApplicationImage.handle, lookup_withDeadlines]
      cases image.lookup address with
      | none => rfl
      | some instruction => cases instruction <;> rfl
  | binding address handle =>
      simp only [ApplicationImage.handle, lookup_withDeadlines]
      cases image.lookup address with
      | none => rfl
      | some instruction => cases instruction <;> rfl
  | conditional address request =>
      simp only [ApplicationImage.handle, lookup_withDeadlines]
      cases image.lookup address with
      | none => rfl
      | some instruction =>
          cases instruction with
          | sample code | bind code | publicChoice code => rfl
          | conditional code =>
              exact conditional_handle_withDeadline_eq code
                (deadlineOf code.endpoint.publicationNode) state id request
                  (by cases request <;> exact hindependent)

/-- Ordered admission is deadline-independent as well: retiming preserves the
active address and the admitted non-expiry handler is unchanged. -/
theorem ordered_handle_withDeadlines_eq (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (state : State P L) (message : Message P (Payload P L))
    (hindependent : message.payload.DeadlineIndependent) :
    (image.withDeadlines deadlineOf).orderedApplication.handle state message =
      image.orderedApplication.handle state message := by
  simp only [orderedApplication, Interaction.MessageApplication.withAdmission]
  change (if (image.withDeadlines deadlineOf).admitsMessage state.memory message then
      (image.withDeadlines deadlineOf).handle state message else none) =
    (if image.admitsMessage state.memory message then image.handle state message else none)
  have hadmits : (image.withDeadlines deadlineOf).admitsMessage state.memory message =
      image.admitsMessage state.memory message := by
    unfold admitsMessage admitsAddress
    cases message.payload.address? <;> simp
  rw [hadmits, image.handle_withDeadlines_eq deadlineOf state message hindependent]

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.handle_withDeadlines_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.handle_withDeadlines_eq

/-- info: 'Vegas.ApplicationImage.ordered_handle_withDeadlines_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_handle_withDeadlines_eq
