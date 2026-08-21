/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.EVMDeployment
import Vegas.Machine.Contract.ClassicalEVMBytes

/-!
# Executable semantics for the emitted EVM subset

This module gives the reified EVM instructions an explicit gas-free execution
semantics. Program counters and jump destinations are byte offsets, pushes use
their emitted big-endian payload, calldata is zero-padded as on EVM, storage is
total, and memory/log/return/revert effects are concrete byte sequences.

The semantics deliberately faults on operations the current Vegas backend does
not emit (`KECCAK256` is the only such nontrivial operation). Gas accounting,
call frames, and chain transaction scheduling are later refinements. This is a
classical target semantics, not yet the theorem that generated handlers refine
the typed classical contract.
-/

namespace Vegas.Machine.Contract.EVM

/-- Interpret a big-endian byte string as one 256-bit EVM word. -/
def bytesToWord (bytes : List Byte) : Word :=
  BitVec.ofNat 256 <|
    bytes.foldl (fun value next => value * 256 + next.toNat) 0

/-- Read a fixed number of bytes, padding beyond the input with zero. -/
def readBytes (bytes : List Byte) (offset count : Nat) : List Byte :=
  List.ofFn fun index : Fin count => bytes[offset + index]?.getD 0

@[simp] theorem readBytes_length (bytes : List Byte) (offset count : Nat) :
    (readBytes bytes offset count).length = count := by
  simp [readBytes]

/-- One EVM `CALLDATALOAD`. -/
def calldataLoad (calldata : List Byte) (offset : Nat) : Word :=
  bytesToWord (readBytes calldata offset 32)

/-- Big-endian byte sequence represented by dependent byte calldata. -/
def ByteCalldata.bytes (calldata : ByteCalldata) : List Byte :=
  List.ofFn fun index : Fin calldata.byteLength =>
    calldata.bits.extractLsb'
      (8 * (calldata.byteLength - 1 - (index : Nat))) 8

@[simp] theorem ByteCalldata.bytes_length (calldata : ByteCalldata) :
    calldata.bytes.length = calldata.byteLength := by
  simp [ByteCalldata.bytes]

/-- Byte-addressed volatile EVM memory. -/
abbrev Memory := Nat → Byte

/-- Initially zero EVM memory. -/
def emptyMemory : Memory := fun _ => 0

/-- Write a byte string to consecutive memory addresses. -/
def writeBytes (memory : Memory) (offset : Nat) : List Byte → Memory
  | [] => memory
  | value :: rest =>
      writeBytes (Function.update memory offset value) (offset + 1) rest

/-- Read consecutive bytes from memory. -/
def readMemory (memory : Memory) (offset count : Nat) : List Byte :=
  List.ofFn fun index : Fin count => memory (offset + index)

@[simp] theorem readMemory_length (memory : Memory) (offset count : Nat) :
    (readMemory memory offset count).length = count := by
  simp [readMemory]

/-- Environment fixed for one EVM call or creation execution. -/
structure ExecutionEnv where
  codeBytes : List Byte
  calldata : List Byte
  caller : AddressWord
  contractAddress : AddressWord
  callValue : Word

/-- Terminal reason of one execution. `fault` covers stack underflow, invalid
jumps, unsupported opcodes, and running past the code. -/
inductive Exit where
  | stopped
  | returned (data : List Byte)
  | reverted (data : List Byte)
  | fault
deriving DecidableEq

/-- Gas-free state of one execution. Stack head is the EVM top of stack. -/
structure ExecutionState where
  pc : Nat
  stack : List Word
  memory : Memory
  storage : TotalStorage
  logs : List (List Byte)
  exit : Option Exit

/-- Initial state of one call over supplied account storage. -/
def ExecutionState.initial (storage : TotalStorage) : ExecutionState where
  pc := 0
  stack := []
  memory := emptyMemory
  storage := storage
  logs := []
  exit := none

/-- Fetch an instruction only at an instruction boundary denoted by its byte
offset. Landing inside a push payload returns `none`. -/
def Assembly.fetch? : Assembly → Nat → Option Instruction
  | [], _ => none
  | instruction :: rest, offset =>
      if offset = 0 then some instruction
      else if offset < instruction.byteLength then none
      else Assembly.fetch? rest (offset - instruction.byteLength)

@[simp] theorem Assembly.fetch?_zero (instruction : Instruction)
    (rest : Assembly) :
    Assembly.fetch? (instruction :: rest) 0 = some instruction :=
  by simp [Assembly.fetch?]

/-- Skipping one leading instruction by its encoded byte length lands at the
same offset in the remaining assembly. -/
theorem Assembly.fetch?_add_byteLength (instruction : Instruction)
    (rest : Assembly) (offset : Nat) :
    Assembly.fetch? (instruction :: rest)
        (instruction.byteLength + offset) =
      Assembly.fetch? rest offset := by
  cases instruction <;>
    simp [Assembly.fetch?, Instruction.byteLength]

/-- Fetching after an arbitrary emitted prefix is exactly fetching from the
following suffix at offset zero. -/
theorem Assembly.fetch?_append_byteLength (pre suffix : Assembly) :
    Assembly.fetch? (pre ++ suffix) pre.byteLength =
      Assembly.fetch? suffix 0 := by
  induction pre with
  | nil => rfl
  | cons instruction rest ih =>
      change
        Assembly.fetch? (instruction :: (rest ++ suffix))
            (instruction.byteLength + Assembly.byteLength rest) = _
      calc
        _ = Assembly.fetch? (rest ++ suffix) (Assembly.byteLength rest) :=
          Assembly.fetch?_add_byteLength instruction (rest ++ suffix)
            (Assembly.byteLength rest)
        _ = Assembly.fetch? suffix 0 := ih

/-- A fragment begins at one byte offset inside a whole assembly program. -/
def Assembly.CodeAt (whole fragment : Assembly) (offset : Nat) : Prop :=
  ∃ pre suffix,
    whole = pre ++ fragment ++ suffix ∧ pre.byteLength = offset

/-- Successful symbolic resolution places an embedded straight-line fragment
at the byte offset of its symbolic prefix. -/
theorem LocalAssembly.resolveAt_codeAt
    {base : Nat} {program pre suffix : LocalAssembly}
    {fragment resolved : Assembly}
    (hprogram : program = pre ++ LocalAssembly.ofAssembly fragment ++ suffix)
    (hresolve : program.resolveAt base = some resolved) :
    Assembly.CodeAt resolved fragment pre.byteLength := by
  rcases LocalAssembly.resolveAt_decomposition hprogram hresolve with
    ⟨preCode, suffixCode, hresolved, hlength⟩
  exact ⟨preCode, suffixCode, hresolved, hlength⟩

/-- `CodeAt` makes fetching the fragment's first instruction exact. -/
theorem Assembly.fetch?_of_codeAt {whole rest : Assembly} {offset : Nat}
    {instruction : Instruction}
    (hcode : Assembly.CodeAt whole (instruction :: rest) offset) :
    whole.fetch? offset = some instruction := by
  rcases hcode with ⟨pre, suffix, rfl, hoffset⟩
  rw [← hoffset]
  rw [List.append_assoc]
  rw [Assembly.fetch?_append_byteLength]
  rfl

/-- Advancing by the first instruction's byte length preserves `CodeAt` for
the remaining fragment. -/
theorem Assembly.CodeAt.tail {whole rest : Assembly} {offset : Nat}
    {instruction : Instruction}
    (hcode : Assembly.CodeAt whole (instruction :: rest) offset) :
    Assembly.CodeAt whole rest (offset + instruction.byteLength) := by
  rcases hcode with ⟨pre, suffix, hwhole, hoffset⟩
  refine ⟨pre ++ [instruction], suffix, ?_, ?_⟩
  · simpa [List.append_assoc] using hwhole
  · rw [Assembly.byteLength_append, hoffset]
    simp [Assembly.byteLength, Instruction.byteLength]

/-- A leading subfragment starts at the same certified offset. -/
theorem Assembly.CodeAt.left {whole left right : Assembly} {offset : Nat}
    (hcode : Assembly.CodeAt whole (left ++ right) offset) :
    Assembly.CodeAt whole left offset := by
  rcases hcode with ⟨pre, suffix, hwhole, hoffset⟩
  refine ⟨pre, right ++ suffix, ?_, hoffset⟩
  simpa [List.append_assoc] using hwhole

/-- The trailing subfragment starts after the leading fragment's emitted byte
length. -/
theorem Assembly.CodeAt.right {whole left right : Assembly} {offset : Nat}
    (hcode : Assembly.CodeAt whole (left ++ right) offset) :
    Assembly.CodeAt whole right (offset + left.byteLength) := by
  rcases hcode with ⟨pre, suffix, hwhole, hoffset⟩
  refine ⟨pre ++ left, suffix, ?_, ?_⟩
  · simpa [List.append_assoc] using hwhole
  · rw [Assembly.byteLength_append, hoffset]

/-- Whether a byte destination is a valid `JUMPDEST`. -/
def Assembly.validJumpDest (program : Assembly) (destination : Nat) : Bool :=
  match program.fetch? destination with
  | some .jumpdest => true
  | _ => false

/-- Advance to the byte following an instruction. -/
def advance (state : ExecutionState) (instruction : Instruction)
    (stack : List Word := state.stack) : ExecutionState :=
  { state with
    pc := state.pc + instruction.byteLength
    stack := stack }

/-- Fault the current execution. -/
def fault (state : ExecutionState) : ExecutionState :=
  { state with exit := some .fault }

/-- Canonical Boolean EVM result word. -/
def boolWord (condition : Bool) : Word :=
  if condition then 1 else 0

/-- Execute one instruction at the current byte program counter. -/
def stepInstruction (program : Assembly) (env : ExecutionEnv)
    (instruction : Instruction) (state : ExecutionState) : ExecutionState :=
  match instruction with
  | .stop => { state with exit := some .stopped }
  | .push data => advance state instruction (data.value :: state.stack)
  | .pop =>
      match state.stack with
      | _ :: rest => advance state instruction rest
      | [] => fault state
  | .dup index =>
      match state.stack[index]? with
      | some value => advance state instruction (value :: state.stack)
      | none => fault state
  | .swap index =>
      let target := index + 1
      match state.stack, state.stack[target]? with
      | top :: _, some value =>
          let swapped := (state.stack.set target top).set 0 value
          advance state instruction swapped
      | _, _ => fault state
  | .add | .mul | .sub | .div | .mod | .lt | .gt | .eq | .and | .or |
      .xor | .shl | .shr =>
      match state.stack with
      | right :: left :: rest =>
          let result :=
            match instruction with
            | .add => left + right
            | .mul => left * right
            | .sub => left - right
            | .div => if right = 0 then 0 else left / right
            | .mod => if right = 0 then 0 else left % right
            | .lt => boolWord (left.toNat < right.toNat)
            | .gt => boolWord (left.toNat > right.toNat)
            | .eq => boolWord (left = right)
            | .and => left &&& right
            | .or => left ||| right
            | .xor => left ^^^ right
            | .shl => left <<< right.toNat
            | .shr => left >>> right.toNat
            | _ => 0
          advance state instruction (result :: rest)
      | _ => fault state
  | .iszero =>
      match state.stack with
      | value :: rest =>
          advance state instruction (boolWord (value = 0) :: rest)
      | [] => fault state
  | .not =>
      match state.stack with
      | value :: rest => advance state instruction (~~~value :: rest)
      | [] => fault state
  | .caller =>
      advance state instruction
        (BitVec.ofNat 256 env.caller.toNat :: state.stack)
  | .address =>
      advance state instruction
        (BitVec.ofNat 256 env.contractAddress.toNat :: state.stack)
  | .callvalue => advance state instruction (env.callValue :: state.stack)
  | .calldatasize =>
      advance state instruction
        (BitVec.ofNat 256 env.calldata.length :: state.stack)
  | .calldataload =>
      match state.stack with
      | offset :: rest =>
          advance state instruction
            (calldataLoad env.calldata offset.toNat :: rest)
      | [] => fault state
  | .mload =>
      match state.stack with
      | offset :: rest =>
          advance state instruction
            (bytesToWord (readMemory state.memory offset.toNat 32) :: rest)
      | [] => fault state
  | .mstore =>
      match state.stack with
      | offset :: value :: rest =>
          { advance state instruction rest with
            memory := writeBytes state.memory offset.toNat
              (PushData.word value).bytes }
      | _ => fault state
  | .sload =>
      match state.stack with
      | key :: rest =>
          advance state instruction (state.storage key.toNat :: rest)
      | [] => fault state
  | .sstore =>
      match state.stack with
      | key :: value :: rest =>
          { advance state instruction rest with
            storage := Function.update state.storage key.toNat value }
      | _ => fault state
  | .jump =>
      match state.stack with
      | destination :: rest =>
          if program.validJumpDest destination.toNat then
            { state with pc := destination.toNat, stack := rest }
          else
            fault state
      | [] => fault state
  | .jumpi =>
      match state.stack with
      | destination :: condition :: rest =>
          if condition = 0 then advance state instruction rest
          else if program.validJumpDest destination.toNat then
            { state with pc := destination.toNat, stack := rest }
          else
            fault state
      | _ => fault state
  | .pc =>
      advance state instruction (BitVec.ofNat 256 state.pc :: state.stack)
  | .jumpdest => advance state instruction
  | .log0 =>
      match state.stack with
      | offset :: size :: rest =>
          { advance state instruction rest with
            logs := state.logs ++
              [readMemory state.memory offset.toNat size.toNat] }
      | _ => fault state
  | .return =>
      match state.stack with
      | offset :: size :: rest =>
          { state with
            stack := rest
            exit := some (.returned
              (readMemory state.memory offset.toNat size.toNat)) }
      | _ => fault state
  | .revert =>
      match state.stack with
      | offset :: size :: rest =>
          { state with
            stack := rest
            exit := some (.reverted
              (readMemory state.memory offset.toNat size.toNat)) }
      | _ => fault state
  | .codecopy =>
      match state.stack with
      | destination :: source :: size :: rest =>
          { advance state instruction rest with
            memory := writeBytes state.memory destination.toNat
              (readBytes env.codeBytes source.toNat size.toNat) }
      | _ => fault state
  | .keccak256 | .invalid => fault state

/-- Execute one fetched EVM instruction. Terminal states are stable. -/
def step (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) : ExecutionState :=
  match state.exit with
  | some _ => state
  | none =>
      match program.fetch? state.pc with
      | none => fault state
      | some instruction => stepInstruction program env instruction state

/-- A running state at a certified code fragment executes that fragment's
first instruction. -/
theorem step_of_codeAt {program rest : Assembly} {env : ExecutionEnv}
    {state : ExecutionState} {instruction : Instruction}
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt program (instruction :: rest) state.pc) :
    step program env state = stepInstruction program env instruction state := by
  simp [step, hrunning, Assembly.fetch?_of_codeAt hcode]

@[simp] theorem step_of_exit (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (exit : Exit) (hexit : state.exit = some exit) :
    step program env state = state := by
  simp [step, hexit]

/-- Fuel-bounded execution. Generated acyclic handlers have a structural
fuel bound; fuel is explicit here so arbitrary reified assembly remains total.
-/
def run : Nat → Assembly → ExecutionEnv → ExecutionState → ExecutionState
  | 0, _, _, state => state
  | fuel + 1, program, env, state =>
      match state.exit with
      | some _ => state
      | none => run fuel program env (step program env state)

@[simp] theorem run_of_exit (fuel : Nat) (program : Assembly)
    (env : ExecutionEnv) (state : ExecutionState) (exit : Exit)
    (hexit : state.exit = some exit) :
    run fuel program env state = state := by
  cases fuel <;> simp [run, hexit]

/-- Fuel composition: running two step budgets successively is the same as
running their sum. Terminal-state stability makes the law exact. -/
theorem run_add (first second : Nat) (program : Assembly)
    (env : ExecutionEnv) (state : ExecutionState) :
    run (first + second) program env state =
      run second program env (run first program env state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
      cases hexit : state.exit with
      | none =>
          rw [show Nat.succ first + second = (first + second) + 1 by omega]
          simp only [run, hexit]
          exact ih (step program env state)
      | some exit => simp [run, hexit, run_of_exit]

/-- Peel one certified instruction from a fuel-bounded execution. -/
theorem run_succ_of_codeAt {program rest : Assembly} {env : ExecutionEnv}
    {state : ExecutionState} {instruction : Instruction} (fuel : Nat)
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt program (instruction :: rest) state.pc) :
    run (fuel + 1) program env state =
      run fuel program env
        (stepInstruction program env instruction state) := by
  simp [run, hrunning, step_of_codeAt hrunning hcode]

/-- A reified fragment executes sequentially without exiting or changing its
next byte address unexpectedly. This deliberately excludes taken jumps. -/
def StraightRun (program : Assembly) (env : ExecutionEnv) :
    Assembly → ExecutionState → ExecutionState → Prop
  | [], state, result => result = state
  | instruction :: rest, state, result =>
      state.exit = none ∧
      (stepInstruction program env instruction state).pc =
        state.pc + instruction.byteLength ∧
      StraightRun program env rest
        (stepInstruction program env instruction state) result

/-- A certified sequential fragment agrees with fuel-bounded execution for
exactly one step per instruction. -/
theorem StraightRun.run_eq {program fragment : Assembly} {env : ExecutionEnv}
    {state result : ExecutionState}
    (hstraight : StraightRun program env fragment state result)
    (hcode : Assembly.CodeAt program fragment state.pc) :
    run fragment.length program env state = result := by
  induction fragment generalizing state result with
  | nil =>
      change result = state at hstraight
      change state = result
      exact hstraight.symm
  | cons instruction rest ih =>
      rcases hstraight with ⟨hrunning, hpc, hrest⟩
      rw [List.length_cons, run_succ_of_codeAt rest.length hrunning hcode]
      apply ih hrest
      have htail := hcode.tail
      rw [← hpc] at htail
      exact htail

/-- The two-instruction pattern used for an event's result write stores the
existing stack top at the pushed key and otherwise falls through. -/
theorem run_push_sstore (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (key : PushData) (value : Word)
    (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = value :: rest)
    (hcode : Assembly.CodeAt program [.push key, .sstore] state.pc) :
    run 2 program env state =
      { state with
        pc := state.pc + (.push key : Instruction).byteLength + 1
        stack := rest
        storage := Function.update state.storage key.value.toNat value } := by
  let pushed : ExecutionState :=
    advance state (.push key) (key.value :: value :: rest)
  have hpush : step program env state = pushed := by
    rw [step_of_codeAt hrunning hcode]
    simp [stepInstruction, pushed, hstack]
  have htail := hcode.tail
  have htail' :
      Assembly.CodeAt program [.sstore] pushed.pc := by
    simpa [pushed, advance] using htail
  let stored : ExecutionState :=
    { pushed with
      pc := pushed.pc + 1
      stack := rest
      storage := Function.update state.storage key.value.toNat value }
  have hpushedRunning : pushed.exit = none := by
    simp [pushed, advance, hrunning]
  have hstore : step program env pushed = stored := by
    rw [step_of_codeAt hpushedRunning htail']
    simp [stepInstruction, stored, pushed, advance,
      Instruction.byteLength]
  have hrunPush : run 1 program env state = pushed := by
    simp [run, hrunning, hpush]
  have hrunStore : run 1 program env pushed = stored := by
    simp [run, hpushedRunning, hstore]
  rw [show 2 = 1 + 1 by omega, run_add]
  rw [hrunPush, hrunStore]
  simp [stored, pushed, advance, Instruction.byteLength]

/-- The three-instruction constant-write pattern used for administrative bits
stores the pushed value and preserves the prior stack. -/
theorem run_push_push_sstore (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (value key : PushData)
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt program
      [.push value, .push key, .sstore] state.pc) :
    run 3 program env state =
      { state with
        pc := state.pc + (.push value : Instruction).byteLength +
          (.push key : Instruction).byteLength + 1
        storage := Function.update state.storage key.value.toNat value.value } := by
  let pushed : ExecutionState :=
    advance state (.push value) (value.value :: state.stack)
  have hpush : step program env state = pushed := by
    rw [step_of_codeAt hrunning hcode]
    simp [stepInstruction, pushed]
  have htail := hcode.tail
  have htail' :
      Assembly.CodeAt program [.push key, .sstore] pushed.pc := by
    simpa [pushed, advance] using htail
  have hpushedRunning : pushed.exit = none := by
    simp [pushed, advance, hrunning]
  have hrunPush : run 1 program env state = pushed := by
    simp [run, hrunning, hpush]
  have hrunStore :=
    run_push_sstore program env pushed key value.value state.stack
      hpushedRunning rfl htail'
  rw [show 3 = 1 + 2 by omega, run_add, hrunPush, hrunStore]
  simp [pushed, advance, Instruction.byteLength]

/-- Execute from the standard empty-stack/memory state. -/
def execute (fuel : Nat) (program : Assembly) (env : ExecutionEnv)
    (storage : TotalStorage) : ExecutionState :=
  run fuel program env (ExecutionState.initial storage)

/-- Transaction-level projection. Revert and fault carry no successor storage,
so rollback is structural rather than an additional theorem premise. -/
inductive TransactionResult where
  | success (storage : TotalStorage) (logs : List (List Byte))
      (returnData : List Byte)
  | revert (data : List Byte)
  | fault
  | outOfFuel

/-- Commit state only after normal `STOP`/`RETURN`; every revert discards all
intermediate writes. -/
def ExecutionState.transactionResult
    (state : ExecutionState) : TransactionResult :=
  match state.exit with
  | some .stopped => .success state.storage state.logs []
  | some (.returned data) => .success state.storage state.logs data
  | some (.reverted data) => .revert data
  | some .fault => .fault
  | none => .outOfFuel

/-- Run one transaction and apply the rollback-aware result projection. -/
def executeTransaction (fuel : Nat) (program : Assembly)
    (env : ExecutionEnv) (storage : TotalStorage) : TransactionResult :=
  (execute fuel program env storage).transactionResult

/-- Fresh EVM account storage before constructor execution. -/
def freshStorage : TotalStorage := fun _ => 0

namespace DeploymentImage

variable {selectors : ClassicalSelectors}

/-- Execute creation assembly against its actual appended creation bytes.
The program is acyclic, so one step per assembly instruction is sufficient. -/
def execute (image : DeploymentImage selectors) : ExecutionState :=
  EVM.execute (image.creationAssembly.length + 1) image.creationAssembly
    { codeBytes := image.bytecode
      calldata := []
      caller := 0
      contractAddress := 0
      callValue := 0 }
    freshStorage

end DeploymentImage

end Vegas.Machine.Contract.EVM
