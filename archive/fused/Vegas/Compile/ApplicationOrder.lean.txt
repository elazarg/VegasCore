/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage
import Interaction.MessageApplicationAdmission

/-! # Source-ordered admission for public applications

This optional application instance admits only the first unfinished emitted
instruction. Selection uses immutable code and public completion flags. The
ordinary graph-enabled application remains available with its original
semantics. Both instances use the shared message runner and the same policy,
observation, and raw-command types.

Premature messages may be submitted, delivered, replayed, and included. Their
inclusion is rejected without an application update; the ledger and rejection
receipt remain observable. Successful resolution changes the next admissible
instruction immediately. No service-cycle boundary, clock origin, fairness,
or strategic correspondence is supplied by this admission rule.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The requested dispatch address, including the address of a timeout call.
Malformed top-level traffic has no dispatch address. -/
def Payload.address? : Payload P L → Option Nat
  | .choice address _ | .expireChoice address | .binding address _ |
      .expireBinding address | .conditional address _ => some address
  | .malformed _ => none

/-- The first unfinished instruction's completion address. For generated
public and conditional instructions, the adjacent source pair completes
atomically and this address is the publication node. -/
def activeAddress? (image : ApplicationImage P L) (memory : Memory P L) : Option Nat :=
  (image.instructions.find? fun instruction => !memory.done instruction.address).map
    ApplicationInstruction.address

/-- Application admission depends on public completion state, not private
preparation, frozen openings, or a source interpreter. -/
def admitsAddress (image : ApplicationImage P L) (memory : Memory P L)
    (address : Nat) : Bool :=
  image.activeAddress? memory == some address

def admitsMessage (image : ApplicationImage P L) (memory : Memory P L)
    (message : Message P (Payload P L)) : Bool :=
  match message.payload.address? with
  | none => false
  | some address => image.admitsAddress memory address

def admitsEnvironment (image : ApplicationImage P L) (memory : Memory P L) :
    EnvironmentCommand → Bool
  | .advance _ => true
  | .sample address => image.admitsAddress memory address

/-- The ordered protocol is an admission instance of the same native
application. It adds no restrictions to the policies' raw command alphabet. -/
def orderedApplication (image : ApplicationImage P L) : MessageApplication P :=
  image.application.withAdmission image.admitsMessage image.admitsEnvironment

omit [DecidableEq P] in
@[simp] theorem admitsAddress_iff (image : ApplicationImage P L)
    (memory : Memory P L) (address : Nat) :
    image.admitsAddress memory address = true ↔
      image.activeAddress? memory = some address := by
  simp [admitsAddress]

omit [DecidableEq P] in
theorem activeAddress?_head (instruction : ApplicationInstruction P L)
    (rest : List (ApplicationInstruction P L)) (memory : Memory P L)
    (hhead : memory.done instruction.address = false) :
    (ApplicationImage.mk (instruction :: rest)).activeAddress? memory =
      some instruction.address := by
  simp [activeAddress?, hhead]

omit [DecidableEq P] in
/-- Completed instruction prefixes do not remain in the admission path. This
does not assume that arbitrary image metadata has unique addresses. -/
theorem activeAddress?_after_completed
    (before : List (ApplicationInstruction P L)) (image : ApplicationImage P L)
    (memory : Memory P L)
    (hbefore : ∀ instruction ∈ before, memory.done instruction.address = true) :
    (ApplicationImage.mk (before ++ image.instructions)).activeAddress? memory =
      image.activeAddress? memory := by
  induction before with
  | nil => rfl
  | cons instruction rest ih =>
      have hhead := hbefore instruction List.mem_cons_self
      have hrest : ∀ prior ∈ rest, memory.done prior.address = true := by
        intro prior hprior
        exact hbefore prior (List.mem_cons_of_mem instruction hprior)
      simpa only [List.cons_append, activeAddress?, List.find?_cons, hhead,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte] using ih hrest

/-- At the admitted address the complete handler is unchanged, including its
ordinary validation and all failure cases. -/
theorem ordered_handle_eq (image : ApplicationImage P L) (state : State P L)
    (message : Message P (Payload P L)) (address : Nat)
    (haddress : message.payload.address? = some address)
    (hactive : image.activeAddress? state.memory = some address) :
    image.orderedApplication.handle state message = image.handle state message := by
  simp [orderedApplication, MessageApplication.withAdmission, application,
    admitsMessage, haddress, admitsAddress, hactive]

/-- A future, completed, or unknown address is rejected if it is not current.
This is a handler result; inclusion still records the message and receipt. -/
theorem ordered_handle_reject (image : ApplicationImage P L) (state : State P L)
    (message : Message P (Payload P L)) (address : Nat)
    (haddress : message.payload.address? = some address)
    (hinactive : image.activeAddress? state.memory ≠ some address) :
    image.orderedApplication.handle state message = none := by
  simp [orderedApplication, MessageApplication.withAdmission, application,
    admitsMessage, haddress, admitsAddress, hinactive]

theorem ordered_handle_malformed (image : ApplicationImage P L) (state : State P L)
    (id : MessageId P) (data : List Nat) :
    image.orderedApplication.handle state ⟨id, .malformed data⟩ = none := rfl

theorem ordered_sample_eq (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (hactive : image.activeAddress? state.memory = some address) :
    image.orderedApplication.environmentStep state (.sample address) =
      image.sample state address := by
  simp [orderedApplication, MessageApplication.withAdmission, application,
    admitsEnvironment, admitsAddress, hactive]

theorem ordered_sample_inactive (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (hinactive : image.activeAddress? state.memory ≠ some address) :
    image.orderedApplication.environmentStep state (.sample address) = FinDist.pure state := by
  simp [orderedApplication, MessageApplication.withAdmission, application,
    admitsEnvironment, admitsAddress, hinactive]

@[simp] theorem ordered_advance (image : ApplicationImage P L) (state : State P L)
    (clock : Nat) :
    image.orderedApplication.environmentStep state (.advance clock) =
      FinDist.pure (state.advance clock) := rfl

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.ordered_handle_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_handle_eq

/-- info: 'Vegas.ApplicationImage.ordered_sample_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_sample_eq
