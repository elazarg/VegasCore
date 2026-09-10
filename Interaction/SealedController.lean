/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies
import Interaction.SealedApplication
import Interaction.SealedProgramLaws

/-! # Public-view controllers for sealed-message openings -/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

def openingCommand [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (owner : Principal) (revealNode : Nat) (value : Value)
    (view : (program.messageApplication (Value := Value)).View) :
    (program.messageApplication (Value := Value)).PlayerCommand :=
  match openingRequest? program view.application owner revealNode value with
  | some payload => .submit payload
  | none => .wait

def openingPolicy [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (owner : Principal) (revealNode : Nat)
    (value : Value) : (program.messageApplication (Value := Value)).PlayerPolicy :=
  fun _ view => FinDist.pure (openingCommand program owner revealNode value view)

/-- The owner's complete local controller: privately register, publish the
opaque commitment, then use the public-view opening controller. -/
def commitOpenPolicy [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (owner : Principal)
    (commitNode revealNode : Nat) (value : Value) :
    (program.messageApplication (Value := Value)).PlayerPolicy :=
  fun history view =>
    match history.length with
    | 0 => FinDist.pure (.privateCommand ⟨(commitNode, value)⟩)
    | 1 => FinDist.pure (.submit (.commitment commitNode (owner, commitNode)))
    | _ + 2 => openingPolicy program owner revealNode value history view

theorem openingCommand_eq_wait_of_handle_eq_none
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (owner : Principal) (revealNode : Nat)
    (value : Value) (view : (program.messageApplication (Value := Value)).View)
    (hready : openingHandle? program view.application owner revealNode = none) :
    openingCommand program owner revealNode value view = .wait := by
  simp [openingCommand, openingRequest?, hready]

/-- Public readiness is exactly the condition under which the opening
controller submits, for every chosen value. -/
theorem openingCommand_ne_wait_iff_ready
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (owner : Principal) (revealNode : Nat)
    (value : Value) (view : (program.messageApplication (Value := Value)).View) :
    openingCommand program owner revealNode value view ≠ .wait ↔
      openingReady program view.application owner revealNode = true := by
  cases hhandle : openingHandle? program view.application owner revealNode <;>
    simp [openingCommand, openingRequest?, openingReady, hhandle]

theorem openingCommand_submit_sound
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (owner : Principal) (node source : Nat)
    (value : Value) (view : (program.messageApplication (Value := Value)).View)
    (hcommand : openingCommand program owner node value view =
      .submit (.opening node (owner, source) value)) :
    ∃ requires,
      program.rules[node]? = some { kind := .reveal owner source, requires } ∧
      done view.application node = false ∧
      requires.all (done view.application) = true ∧
      accepted? view.application source = some (owner, source) := by
  unfold openingCommand at hcommand
  split at hcommand
  next payload hrequest =>
    have hpayload : payload = .opening node (owner, source) value := by
      simpa using hcommand
    subst payload
    exact openingRequest?_sound program view.application owner node source value hrequest
  next => contradiction

theorem openingCommand_ne_wait_sound
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (owner : Principal) (node : Nat)
    (value : Value) (view : (program.messageApplication (Value := Value)).View)
    (hnonwait : openingCommand program owner node value view ≠ .wait) :
    ∃ source requires,
      openingCommand program owner node value view =
          .submit (.opening node (owner, source) value) ∧
        program.rules[node]? = some { kind := .reveal owner source, requires } ∧
        done view.application node = false ∧
        requires.all (done view.application) = true ∧
        accepted? view.application source = some (owner, source) := by
  unfold openingCommand at hnonwait ⊢
  cases hrequest : openingRequest? program view.application owner node value with
  | none => simp [hrequest] at hnonwait
  | some payload =>
      have hshape : ∃ source, payload = .opening node (owner, source) value := by
        unfold openingRequest? at hrequest
        cases hhandle : openingHandle? program view.application owner node with
        | none => simp [hhandle] at hrequest
        | some handle =>
            rw [hhandle] at hrequest
            have hpayload : payload = .opening node handle value := by
              simpa using (Option.some.inj hrequest).symm
            subst payload
            obtain ⟨source, rfl⟩ :=
              openingHandle?_eq_some_owner program view.application owner node handle hhandle
            exact ⟨source, rfl⟩
      obtain ⟨source, rfl⟩ := hshape
      refine ⟨source, ?_⟩
      obtain ⟨requires, hrule, hdone, hrequires, haccepted⟩ :=
        openingRequest?_sound program view.application owner node source value hrequest
      exact ⟨requires, rfl, hrule, hdone, hrequires, haccepted⟩

end Interaction.SealedProgram
