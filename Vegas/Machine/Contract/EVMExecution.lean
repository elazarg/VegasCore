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
  | instruction :: _, 0 => some instruction
  | instruction :: rest, offset + 1 =>
      if offset + 1 < instruction.byteLength then none
      else Assembly.fetch? rest (offset + 1 - instruction.byteLength)

@[simp] theorem Assembly.fetch?_zero (instruction : Instruction)
    (rest : Assembly) :
    Assembly.fetch? (instruction :: rest) 0 = some instruction :=
  rfl

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
