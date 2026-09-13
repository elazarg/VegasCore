/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ChoiceControllerHistory
import Interaction.MessageApplicationPolicyInvariant
import Interaction.SealedApplication
import Interaction.SealedProgramLaws

/-! # Local memory of private sealed registrations

The canonical encoding records a slot's first registered value in the owner's
command history. This memory agrees with the ideal service after every native
policy execution from the empty service. Opponents and the environment can
adapt, submit arbitrary payloads, and deliver or include pending messages;
none of those commands can register another principal's slots.
-/

noncomputable section

namespace Interaction.SealedProgram

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- A node-tagged private command; a command for a different slot does not
decode as a choice at this slot. -/
def registrationEncoding (program : SealedProgram Principal) (slot : Nat) :
    ChoiceEncoding Value (program.messageApplication (Value := Value)).PlayerCommand where
  encode value := .privateCommand ⟨(slot, value)⟩
  decode
    | .privateCommand command => if command.down.1 = slot then some command.down.2 else none
    | _ => none
  decode_encode _ := by simp
  decode_sound command value hdecode := by
    cases command with
    | privateCommand command =>
        rcases command with ⟨other, stored⟩
        dsimp only at hdecode
        split at hdecode
        · rename_i hslot
          cases hslot
          cases Option.some.inj hdecode
          rfl
        · contradiction
    | submit payload | replay id | wait => contradiction

/-- The ideal service is proof-facing; the right side uses only the owner's
local command history. -/
def RegistrationMemory (program : SealedProgram Principal)
    (execution : (program.messageApplication (Value := Value)).PolicyExecution) : Prop :=
  ∀ owner slot, execution.native.application.service.lookup (owner, slot) =
    (program.registrationEncoding slot).cachedValue
      (program.messageApplication (Value := Value)) (execution.principalHistory owner)

namespace RegistrationMemory

variable {program : SealedProgram Principal}

theorem initial : RegistrationMemory program
    (PolicyExecution.initial (program.messageApplication (Value := Value))
      (MessageApplication.State.initial _ ⟨IdealCommitments.empty, []⟩)) := by
  intro owner slot
  rfl

omit [DecidableEq Value] in
private theorem seal_lookup (service : IdealCommitments Principal Nat Value)
    (owner query : Principal) (slot target : Nat) (value : Value) :
    (service.sealValue owner slot value).state.lookup (query, target) =
      if query = owner then
        (service.lookup (query, target)).orElse
          (fun _ => if slot = target then some value else none)
      else service.lookup (query, target) := by
  by_cases howner : query = owner
  · subst query
    by_cases hslot : slot = target
    · subst target
      cases hlookup : service.table owner slot <;>
        simp [IdealCommitments.sealValue, IdealCommitments.lookup, hlookup]
    · cases hlookup : service.table owner slot <;>
        cases htarget : service.table owner target <;>
        simp [IdealCommitments.sealValue, IdealCommitments.lookup, hlookup,
          hslot, Ne.symm hslot, htarget]
  · cases hlookup : service.table owner slot <;>
      simp [IdealCommitments.sealValue, IdealCommitments.lookup, hlookup, howner]

theorem playerStep (execution next : (program.messageApplication (Value := Value)).PolicyExecution)
    (owner : Principal) (command : (program.messageApplication (Value := Value)).PlayerCommand)
    (hmemory : RegistrationMemory program execution)
    (hnext : next ∈ ((program.messageApplication (Value := Value)).playerStep
      owner execution command).support) : RegistrationMemory program next := by
  cases command with
  | privateCommand command =>
      simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      intro query slot
      change (execution.native.application.service.sealValue
        owner command.down.1 command.down.2).state.lookup (query, slot) = _
      rw [seal_lookup]
      by_cases howner : query = owner
      · subst query
        simp only [↓reduceIte, ChoiceEncoding.cachedValue_append,
          ChoiceEncoding.cachedValue_cons, ChoiceEncoding.cachedValue_nil,
          registrationEncoding]
        rw [hmemory]
        by_cases hslot : command.down.1 = slot <;> simp [hslot, registrationEncoding]
      · simp only [if_neg howner]
        exact hmemory query slot
  | submit payload | replay id | wait =>
      simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      intro query slot
      by_cases howner : query = owner
      · subst query
        simp only [↓reduceIte, ChoiceEncoding.cachedValue_append,
          ChoiceEncoding.cachedValue_cons, ChoiceEncoding.cachedValue_nil,
          registrationEncoding]
        exact (hmemory owner slot).trans (by
          change (program.registrationEncoding slot).cachedValue
            (program.messageApplication (Value := Value)) (execution.principalHistory owner) =
            ((program.registrationEncoding slot).cachedValue
              (program.messageApplication (Value := Value))
              (execution.principalHistory owner)).orElse (fun _ => none)
          cases (program.registrationEncoding slot).cachedValue
            (program.messageApplication (Value := Value))
            (execution.principalHistory owner) <;> rfl)
      · simp only [if_neg howner]
        exact hmemory query slot

private theorem include_service
    (state : (program.messageApplication (Value := Value)).State) (id : MessageId Principal) :
    ((program.messageApplication (Value := Value)).includePending state id).application.service =
      state.application.service := by
  unfold MessageApplication.includePending MessagePool.includeApplication
  cases h : state.pool.includePending id with
  | mk message pool =>
      cases message with
      | none => rfl
      | some message =>
          dsimp only [messageApplication]
          cases program.validateMessage? state.application.service
            state.application.events message <;> rfl

theorem environmentStep
    (execution next : (program.messageApplication (Value := Value)).PolicyExecution)
    (command : (program.messageApplication (Value := Value)).EnvironmentPolicyCommand)
    (hmemory : RegistrationMemory program execution)
    (hnext : next ∈ ((program.messageApplication (Value := Value)).environmentPolicyStep
      execution command).support) : RegistrationMemory program next := by
  cases command with
  | application command => exact nomatch command.down
  | deliver observer id | «include» id | wait =>
      simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      intro query slot
      simpa only [include_service] using hmemory query slot

/-- Exact own-slot reconstruction throughout arbitrary policy execution. -/
theorem runPolicies
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : (program.messageApplication (Value := Value)).PolicyExecution)
    (hmemory : RegistrationMemory program execution)
    (hnext : next ∈ ((program.messageApplication (Value := Value)).runPolicies
      players environment schedule execution).support) : RegistrationMemory program next := by
  apply MessageApplication.runPolicies_execution_invariant _ (RegistrationMemory program)
    players environment ?_ ?_ schedule execution next hmemory hnext
  · intro current owner command final hcurrent _ hfinal
    exact playerStep current final owner command hcurrent hfinal
  · intro current command final hcurrent _ hfinal
    exact environmentStep current final command hcurrent hfinal

end RegistrationMemory

end Interaction.SealedProgram
