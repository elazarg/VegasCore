/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationChoiceTimeouts
import Interaction.MessageApplicationHandlerExtension

/-! # Public-message binding expiry

Optional typed expression code enables permissionless binding-expiry requests.
Acceptance installs a public disposition without registering a private value
or changing an existing verifier. Ordinary binding and expiry compete for one
unresolved instruction; the first successful inclusion prevents replacement.

This pass is independent of public-choice timeout decoration. The native
interpreter still accepts arbitrary traffic. The execution-law comparison
below concerns policies that do not submit binding expiry; it does not cover
arbitrary deviations, delivery guarantees, or source legality of selected code.
-/

namespace Vegas

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} {L : IExpr}

namespace ApplicationInstruction

/-- Attach optional fallback code to bindings, retaining all other code. -/
def withBindingTimeouts
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)) :
    ApplicationInstruction P L → ApplicationInstruction P L
  | .bind code => .bind { code with timeout := select code }
  | .sample code => .sample code
  | .publicChoice code => .publicChoice code
  | .conditional code => .conditional code

@[simp] theorem withBindingTimeouts_address
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (instruction : ApplicationInstruction P L) :
    (instruction.withBindingTimeouts select).address = instruction.address := by
  cases instruction <;> rfl

end ApplicationInstruction

namespace ApplicationImage

def withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)) :
    ApplicationImage P L :=
  ⟨image.instructions.map (ApplicationInstruction.withBindingTimeouts select)⟩

@[simp] theorem lookup_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (address : Nat) :
    (image.withBindingTimeouts select).lookup address =
      (image.lookup address).map (ApplicationInstruction.withBindingTimeouts select) := by
  simp [lookup, withBindingTimeouts, List.find?_map]

/-- Binding and public-choice timeouts can be enabled independently, in either order. -/
theorem withBindingTimeouts_withChoiceTimeouts (image : ApplicationImage P L)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)) :
    (image.withBindingTimeouts binding).withChoiceTimeouts choice =
      (image.withChoiceTimeouts choice).withBindingTimeouts binding := by
  have hcommute : ApplicationInstruction.withChoiceTimeouts choice ∘
      ApplicationInstruction.withBindingTimeouts binding =
      ApplicationInstruction.withBindingTimeouts binding ∘
        ApplicationInstruction.withChoiceTimeouts choice := by
    funext instruction
    cases instruction <;> rfl
  simp only [withBindingTimeouts, withChoiceTimeouts, List.map_map, hcommute]

theorem sample_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (state : ApplicationImage.State P L) (address : Nat) :
    (image.withBindingTimeouts select).sample state address = image.sample state address := by
  simp only [sample, lookup_withBindingTimeouts]
  cases image.lookup address with
  | none => rfl
  | some instruction => cases instruction <;> rfl

/-- A traffic condition for the conservativity theorem, not a runtime restriction. -/
def Payload.NotBindingExpiry : Payload P L → Prop
  | .expireBinding _ => False
  | _ => True

theorem handle_withBindingTimeouts [DecidableEq P] (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (state : ApplicationImage.State P L) (message : Message P (Payload P L))
    (hordinary : message.payload.NotBindingExpiry) :
    (image.withBindingTimeouts select).handle state message = image.handle state message := by
  obtain ⟨id, payload⟩ := message
  cases payload with
  | expireBinding address => exact False.elim hordinary
  | malformed data => rfl
  | choice address typed | expireChoice address | binding address commitment
  | conditional address payload =>
      simp only [handle, lookup_withBindingTimeouts]
      cases image.lookup address with
      | none => rfl
      | some instruction => cases instruction <;> rfl

/-- Enabling binding expiry preserves the complete execution law when no such
packet is initially retained or submitted. The environment remains unrestricted
and may inspect, deliver, include, and replay existing traffic. -/
theorem runPolicies_withBindingTimeouts [DecidableEq P] (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (hsubmit : ∀ (execution : image.application.PolicyExecution) (who : P)
      (address : Nat), .submit (.expireBinding address) ∉
        (players who (execution.principalHistory who)
          (MessageApplication.State.observe image.application execution.native who)).support)
    (schedule : List (@Invocation P)) (execution : image.application.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies (fun message => message.payload.NotBindingExpiry)) :
    (image.withBindingTimeouts select).application.runPolicies players environment schedule
        execution = image.application.runPolicies players environment schedule execution := by
  have hsubmitSafe : ∀ (current : image.application.PolicyExecution) (who : P)
      (payload : Payload P L),
      .submit payload ∈ (players who (current.principalHistory who)
        (MessageApplication.State.observe image.application current.native who)).support →
        ∀ serial, (⟨(who, serial), payload⟩ :
          Message P (Payload P L)).payload.NotBindingExpiry := by
    intro current who payload hsupported serial
    cases payload with
    | expireBinding address => exact False.elim (hsubmit current who address hsupported)
    | _ => trivial
  have hlaw := image.application.runPolicies_eq_of_handler_agrees
    (image.withBindingTimeouts select).handle
    (fun message => message.payload.NotBindingExpiry)
    (fun state message hmessage => image.handle_withBindingTimeouts select state message hmessage)
    players environment hsubmitSafe schedule execution hsafe
  have hsample : (image.withBindingTimeouts select).sample = image.sample := by
    funext state address
    exact image.sample_withBindingTimeouts select state address
  simp only [application, MessageApplication.withHandler] at hlaw ⊢
  rw [hsample]
  exact hlaw

variable [DecidableEq P]

/-- Admission uses public state and executable expression code only. -/
theorem handle_expireBinding_accepts (image : ApplicationImage P L)
    (state : ApplicationImage.State P L) (address : Nat) (code : BindingCode P L)
    (hcode : image.lookup address = some (.bind code)) (id : MessageId P)
    (timeout : PublicFallbackCode L code.ty) (htimeout : code.timeout = some timeout)
    (hunbound : state.memory.accepted code.sourceField = none)
    (hnotDone : state.memory.done code.node = false)
    (hrequires : code.requires.all state.memory.done = true)
    (hoverdue : timeout.deadline < state.memory.clock)
    (value : L.Val code.ty)
    (hvalue : timeout.value.evalStore? state.memory.store = some value) :
    image.handle state ⟨id, .expireBinding address⟩ =
      some (state.defaultBind code ⟨code.ty, value⟩) := by
  rw [image.handle_expireBinding state address code hcode id]
  simp [BindingCode.resolveTimeout?, htimeout, hunbound, hnotDone, hrequires, hoverdue, hvalue]

theorem handle_expireBinding_no_timeout (image : ApplicationImage P L)
    (state : ApplicationImage.State P L) (address : Nat) (code : BindingCode P L)
    (hcode : image.lookup address = some (.bind code)) (id : MessageId P)
    (htimeout : code.timeout = none) :
    image.handle state ⟨id, .expireBinding address⟩ = none := by
  rw [image.handle_expireBinding state address code hcode id]
  simp [BindingCode.resolveTimeout?, htimeout]

/-- Either accepted disposition prevents a later expiry from replacing it. -/
theorem handle_expireBinding_after_resolution (image : ApplicationImage P L)
    (state : ApplicationImage.State P L) (address : Nat) (code : BindingCode P L)
    (hcode : image.lookup address = some (.bind code)) (id : MessageId P)
    (hbound : state.memory.accepted code.sourceField ≠ none) :
    image.handle state ⟨id, .expireBinding address⟩ = none := by
  rw [image.handle_expireBinding state address code hcode id]
  cases htimeout : code.timeout <;> simp [BindingCode.resolveTimeout?, htimeout, hbound]

/-- The real pending packet is appended to the ledger with a successful receipt.
No owner message or private registration is synthesized. -/
theorem include_expireBinding (image : ApplicationImage P L)
    (state : image.application.State) (address : Nat) (code : BindingCode P L)
    (hcode : image.lookup address = some (.bind code)) (id : MessageId P)
    (timeout : PublicFallbackCode L code.ty) (htimeout : code.timeout = some timeout)
    (hunbound : state.application.memory.accepted code.sourceField = none)
    (hnotDone : state.application.memory.done code.node = false)
    (hrequires : code.requires.all state.application.memory.done = true)
    (hoverdue : timeout.deadline < state.application.memory.clock)
    (value : L.Val code.ty)
    (hvalue : timeout.value.evalStore? state.application.memory.store = some value)
    (hlookup : state.pool.lookup id = some ⟨id, .expireBinding address⟩) :
    let next := image.application.includePending state id
    next.application = state.application.defaultBind code ⟨code.ty, value⟩ ∧
      next.receipts = state.receipts ++ [(id, true)] ∧
      next.pool.ledger = state.pool.ledger ++ [⟨id, .expireBinding address⟩] ∧
      next.pool.sent = state.pool.sent ∧ next.pool.inbox = state.pool.inbox := by
  exact image.include_accepted state id ⟨id, .expireBinding address⟩
    (state.application.defaultBind code ⟨code.ty, value⟩) hlookup
    (image.handle_expireBinding_accepts state.application address code hcode id timeout htimeout
      hunbound hnotDone hrequires hoverdue value hvalue)

end ApplicationImage

end Vegas

/-- info: 'Vegas.ApplicationImage.runPolicies_withBindingTimeouts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_withBindingTimeouts

/-- info: 'Vegas.ApplicationImage.include_expireBinding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.include_expireBinding
