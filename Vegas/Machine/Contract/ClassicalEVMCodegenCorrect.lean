/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.ClassicalEVMCodegen
import Vegas.Machine.Contract.EVMExecution

/-!
# Execution correctness of structural classical EVM code

These theorems connect generated instruction fragments to the gas-free EVM
semantics. They are compositional over certified byte offsets and retain the
exact ordered storage updates used by the higher-level snapshot proof.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- Successful action-write code stores the existing result word, then the
presence bit, then the completion bit, and preserves the remaining stack. -/
theorem run_classicalActionWrites
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (action : ClassicalActionIR program) (value : Word) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = value :: rest)
    (hcode : Assembly.CodeAt whole
      (classicalActionWritesAssembly action) state.pc) :
    run 8 whole env state =
      { state with
        pc := state.pc +
          (classicalActionWritesAssembly action).byteLength
        stack := rest
        storage := Function.update
          (Function.update
            (Function.update state.storage
              (PushData.nat256 action.valueSlot).value.toNat value)
            (PushData.nat256 action.presenceSlot).value.toNat 1)
          (PushData.nat256 action.completionSlot).value.toNat 1 } := by
  let valueWrite : Assembly :=
    [.push (.nat256 action.valueSlot), .sstore]
  let presenceWrite : Assembly :=
    [.push (.one (byte 1)), .push (.nat256 action.presenceSlot), .sstore]
  let completionWrite : Assembly :=
    [.push (.one (byte 1)), .push (.nat256 action.completionSlot), .sstore]
  have hdecomp :
      classicalActionWritesAssembly action =
        valueWrite ++ presenceWrite ++ completionWrite := by
    rfl
  rw [hdecomp] at hcode ⊢
  have hcode' :
      Assembly.CodeAt whole
        (valueWrite ++ (presenceWrite ++ completionWrite)) state.pc := by
    simpa [List.append_assoc] using hcode
  have hvalueCode : Assembly.CodeAt whole valueWrite state.pc :=
    hcode'.left
  have hafterValueCode :
      Assembly.CodeAt whole (presenceWrite ++ completionWrite)
        (state.pc + valueWrite.byteLength) :=
    hcode'.right
  let afterValue : ExecutionState :=
    { state with
      pc := state.pc + valueWrite.byteLength
      stack := rest
      storage := Function.update state.storage
        (PushData.nat256 action.valueSlot).value.toNat value }
  have hrunValue : run 2 whole env state = afterValue := by
    have hrun := run_push_sstore whole env state
      (PushData.nat256 action.valueSlot) value rest hrunning hstack
    rw [show valueWrite =
      [.push (.nat256 action.valueSlot), .sstore] by rfl] at hvalueCode
    specialize hrun hvalueCode
    simpa [afterValue, valueWrite, Assembly.byteLength,
      Instruction.byteLength] using hrun
  have hpresenceCode :
      Assembly.CodeAt whole presenceWrite afterValue.pc := by
    have := hafterValueCode.left
    simpa [afterValue] using this
  have hafterPresenceCode :
      Assembly.CodeAt whole completionWrite
        (afterValue.pc + presenceWrite.byteLength) := by
    exact hafterValueCode.right
  let afterPresence : ExecutionState :=
    { afterValue with
      pc := afterValue.pc + presenceWrite.byteLength
      storage := Function.update afterValue.storage
        (PushData.nat256 action.presenceSlot).value.toNat 1 }
  have hafterValueRunning : afterValue.exit = none := by
    simp [afterValue, hrunning]
  have hrunPresence : run 3 whole env afterValue = afterPresence := by
    have hrun := run_push_push_sstore whole env afterValue
      (PushData.one (byte 1)) (PushData.nat256 action.presenceSlot)
      hafterValueRunning
    rw [show presenceWrite =
      [.push (.one (byte 1)), .push (.nat256 action.presenceSlot),
        .sstore] by rfl] at hpresenceCode
    specialize hrun hpresenceCode
    simpa [afterPresence, presenceWrite, Assembly.byteLength,
      Instruction.byteLength] using hrun
  have hcompletionCode :
      Assembly.CodeAt whole completionWrite afterPresence.pc := by
    simpa [afterPresence] using hafterPresenceCode
  let afterCompletion : ExecutionState :=
    { afterPresence with
      pc := afterPresence.pc + completionWrite.byteLength
      storage := Function.update afterPresence.storage
        (PushData.nat256 action.completionSlot).value.toNat 1 }
  have hafterPresenceRunning : afterPresence.exit = none := by
    simp [afterPresence, afterValue, hrunning]
  have hrunCompletion :
      run 3 whole env afterPresence = afterCompletion := by
    have hrun := run_push_push_sstore whole env afterPresence
      (PushData.one (byte 1)) (PushData.nat256 action.completionSlot)
      hafterPresenceRunning
    rw [show completionWrite =
      [.push (.one (byte 1)), .push (.nat256 action.completionSlot),
        .sstore] by rfl] at hcompletionCode
    specialize hrun hcompletionCode
    simpa [afterCompletion, completionWrite, Assembly.byteLength,
      Instruction.byteLength] using hrun
  rw [show 8 = 2 + (3 + 3) by omega, run_add, hrunValue,
    run_add, hrunPresence, hrunCompletion]
  simp [afterCompletion, afterPresence, afterValue, valueWrite,
    presenceWrite, completionWrite, Assembly.byteLength,
    Instruction.byteLength]

/-- With the backend's layout-capacity certificate, the same execution writes
the literal natural-number slots rather than merely their modular images. -/
theorem run_classicalActionWrites_exact
    (fits : ClassicalStorageFitsWord program)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (action : ClassicalActionIR program) (value : Word) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = value :: rest)
    (hcode : Assembly.CodeAt whole
      (classicalActionWritesAssembly action) state.pc) :
    run 8 whole env state =
      { state with
        pc := state.pc +
          (classicalActionWritesAssembly action).byteLength
        stack := rest
        storage := Function.update
          (Function.update
            (Function.update state.storage action.valueSlot value)
            action.presenceSlot 1)
          action.completionSlot 1 } := by
  rw [run_classicalActionWrites whole env state action value rest
    hrunning hstack hcode]
  rw [PushData.nat256_value_toNat_of_lt
      (action.valueSlot_lt_word fits),
    PushData.nat256_value_toNat_of_lt
      (action.presenceSlot_lt_word fits),
    PushData.nat256_value_toNat_of_lt
      (action.completionSlot_lt_word fits)]

end

end Vegas.Machine.Contract.EVM
