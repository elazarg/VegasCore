/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.ClassicalEVMCalldata
import Vegas.Machine.Contract.EVMAddress

/-!
# EVM instruction encoding and four-way runtime linking

This module introduces actual EVM runtime bytes, one deliberately small layer
at a time. `Instruction` covers the stack, calldata, caller, storage, control,
log, and termination operations needed by a deterministic Vegas contract.
Every instruction has its Yellow-Paper opcode byte and `emit` concatenates
instruction encodings with a proved byte-length equation.

`RuntimeImage` links four independently compiled handler fragments behind the
classical Vegas selectors. The dispatcher extracts the high 32 bits of the
first calldata word, compares them in stable entry-point order, jumps to the
matching fragment, and reverts for every unknown selector. Handler offsets are
32-bit byte offsets; `LinkableHandlers` carries the corresponding code-size
bound instead of silently truncating an address.

This is runtime-byte generation, not yet a compiler-correctness result. In
particular, the handler fragments still need to be produced by certified
expression, storage, authentication, and oracle-state lowerings, and execution
of the emitted bytes must be related to an EVM semantics.
-/

namespace Vegas.Machine.Contract.EVM

/-- One byte of EVM code. -/
abbrev Byte := BitVec 8

/-- Construct an EVM byte from its numeric opcode. -/
def byte (value : Nat) : Byte := BitVec.ofNat 8 value

/-- A valid immediate payload for `PUSH1` through `PUSH32`. Bytes are stored in
EVM order, most significant first. -/
structure PushData where
  bytes : List Byte
  nonempty : bytes ≠ []
  length_le : bytes.length ≤ 32

namespace PushData

/-- One-byte immediate. -/
def one (value : Byte) : PushData where
  bytes := [value]
  nonempty := by simp
  length_le := by simp

/-- Four-byte immediate. -/
def four (a b c d : Byte) : PushData where
  bytes := [a, b, c, d]
  nonempty := by simp
  length_le := by simp

/-- Big-endian bytes of a 32-bit EVM selector. -/
def selector (value : Selector) : PushData :=
  four
    (value.extractLsb' 24 8)
    (value.extractLsb' 16 8)
    (value.extractLsb' 8 8)
    (value.extractLsb' 0 8)

/-- A natural number encoded as one 32-bit big-endian immediate. Values at or
above `2^32` wrap; linkable runtime images prove that jump destinations never
do so. -/
def nat32 (value : Nat) : PushData :=
  selector (BitVec.ofNat 32 value)

/-- Big-endian bytes of one full EVM word. -/
def word (value : Word) : PushData where
  bytes := List.ofFn fun index : Fin 32 =>
    value.extractLsb' (8 * (31 - (index : Nat))) 8
  nonempty := by simp
  length_le := by simp

/-- Natural number encoded as a full 256-bit immediate. Values at or above
`2^256` wrap; storage-layout backends carry the bound that excludes this. -/
def nat256 (value : Nat) : PushData :=
  word (BitVec.ofNat 256 value)

/-- Big-endian bytes of one native 160-bit EVM account address. -/
def address (value : AddressWord) : PushData where
  bytes := List.ofFn fun index : Fin 20 =>
    value.extractLsb' (8 * (19 - (index : Nat))) 8
  nonempty := by simp
  length_le := by simp

@[simp] theorem one_length (value : Byte) :
    (one value).bytes.length = 1 := by
  rfl

@[simp] theorem selector_length (value : Selector) :
    (selector value).bytes.length = 4 := by
  rfl

@[simp] theorem nat32_length (value : Nat) :
    (nat32 value).bytes.length = 4 := by
  rfl

@[simp] theorem word_length (value : Word) :
    (word value).bytes.length = 32 := by
  simp [word]

@[simp] theorem nat256_length (value : Nat) :
    (nat256 value).bytes.length = 32 := by
  simp [nat256]

@[simp] theorem address_length (value : AddressWord) :
    (address value).bytes.length = 20 := by
  simp [address]

end PushData

/-- Reified EVM operations used by the classical backend. `dup` and `swap`
use zero-based indices: `dup 0` emits `DUP1`, and `swap 0` emits `SWAP1`. -/
inductive Instruction where
  | stop
  | add
  | mul
  | sub
  | div
  | mod
  | lt
  | gt
  | eq
  | iszero
  | and
  | or
  | xor
  | not
  | shl
  | shr
  | keccak256
  | address
  | caller
  | callvalue
  | calldataload
  | calldatasize
  | codecopy
  | pop
  | mload
  | mstore
  | sload
  | sstore
  | jump
  | jumpi
  | pc
  | jumpdest
  | push (data : PushData)
  | dup (index : Fin 16)
  | swap (index : Fin 16)
  | log0
  | return
  | revert
  | invalid

namespace Instruction

/-- Numeric opcode byte of an instruction. Immediate bytes are emitted
separately by `encode`. -/
def opcode : Instruction → Byte
  | .stop => byte 0x00
  | .add => byte 0x01
  | .mul => byte 0x02
  | .sub => byte 0x03
  | .div => byte 0x04
  | .mod => byte 0x06
  | .lt => byte 0x10
  | .gt => byte 0x11
  | .eq => byte 0x14
  | .iszero => byte 0x15
  | .and => byte 0x16
  | .or => byte 0x17
  | .xor => byte 0x18
  | .not => byte 0x19
  | .shl => byte 0x1b
  | .shr => byte 0x1c
  | .keccak256 => byte 0x20
  | .address => byte 0x30
  | .caller => byte 0x33
  | .callvalue => byte 0x34
  | .calldataload => byte 0x35
  | .calldatasize => byte 0x36
  | .codecopy => byte 0x39
  | .pop => byte 0x50
  | .mload => byte 0x51
  | .mstore => byte 0x52
  | .sload => byte 0x54
  | .sstore => byte 0x55
  | .jump => byte 0x56
  | .jumpi => byte 0x57
  | .pc => byte 0x58
  | .jumpdest => byte 0x5b
  | .push data => byte (0x5f + data.bytes.length)
  | .dup index => byte (0x80 + index)
  | .swap index => byte (0x90 + index)
  | .log0 => byte 0xa0
  | .return => byte 0xf3
  | .revert => byte 0xfd
  | .invalid => byte 0xfe

/-- Exact byte encoding of one instruction. -/
def encode : Instruction → List Byte
  | instruction@(.push data) => instruction.opcode :: data.bytes
  | instruction => [instruction.opcode]

/-- Encoded byte length of one instruction. -/
def byteLength : Instruction → Nat
  | .push data => 1 + data.bytes.length
  | _ => 1

@[simp] theorem encode_length (instruction : Instruction) :
    instruction.encode.length = instruction.byteLength := by
  cases instruction <;> simp [encode, byteLength, Nat.add_comm]

@[simp] theorem opcode_push_one (value : Byte) :
    opcode (.push (.one value)) = byte 0x60 := by
  rfl

@[simp] theorem opcode_push_selector (value : Selector) :
    opcode (.push (.selector value)) = byte 0x63 := by
  rfl

@[simp] theorem opcode_push_word (value : Word) :
    opcode (.push (.word value)) = byte 0x7f := by
  simp [opcode]

@[simp] theorem opcode_push_address (value : AddressWord) :
    opcode (.push (.address value)) = byte 0x73 := by
  simp [opcode]

end Instruction

/-- A symbolic EVM instruction program. -/
abbrev Assembly := List Instruction

namespace Assembly

/-- Number of bytes occupied by an instruction program. -/
def byteLength (program : Assembly) : Nat :=
  (program.map Instruction.byteLength).sum

/-- Emit actual EVM bytes. -/
def emit (program : Assembly) : List Byte :=
  program.flatMap Instruction.encode

/-- Emission occupies exactly the statically computed byte length. -/
@[simp] theorem emit_length (program : Assembly) :
    program.emit.length = program.byteLength := by
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
      simp [emit, byteLength]

@[simp] theorem byteLength_append (left right : Assembly) :
    (left ++ right).byteLength = left.byteLength + right.byteLength := by
  simp [byteLength]

@[simp] theorem emit_append (left right : Assembly) :
    (left ++ right).emit = left.emit ++ right.emit := by
  simp [emit]

end Assembly

/-- Four entry points of the deterministic classical contract ABI. -/
inductive ClassicalEntry where
  | player
  | reveal
  | sampleRequest
  | oracleCallback
deriving DecidableEq

/-- Independently compiled runtime fragments for the classical ABI. A handler
is entered with an otherwise empty stack after selector dispatch. -/
structure ClassicalHandlers where
  player : Assembly
  reveal : Assembly
  sampleRequest : Assembly
  oracleCallback : Assembly

namespace ClassicalHandlers

/-- Select one handler fragment. -/
def get (handlers : ClassicalHandlers) : ClassicalEntry → Assembly
  | .player => handlers.player
  | .reveal => handlers.reveal
  | .sampleRequest => handlers.sampleRequest
  | .oracleCallback => handlers.oracleCallback

/-- Each handler begins with `JUMPDEST` and discards the selector retained by
the dispatcher. -/
def block (handlers : ClassicalHandlers) (entry : ClassicalEntry) : Assembly :=
  [.jumpdest, .pop] ++ handlers.get entry

/-- Encoded size of one linked handler block. -/
def blockSize (handlers : ClassicalHandlers) (entry : ClassicalEntry) : Nat :=
  2 + (handlers.get entry).byteLength

@[simp] theorem block_byteLength (handlers : ClassicalHandlers)
    (entry : ClassicalEntry) :
    (handlers.block entry).byteLength = handlers.blockSize entry := by
  simp [block, blockSize, Assembly.byteLength, Instruction.byteLength]
  omega

end ClassicalHandlers

/-- The selector dispatcher is always 64 bytes: 6 bytes to extract the
selector, four 13-byte comparisons with `PUSH4` destinations, and a 6-byte
fallback revert. -/
def classicalDispatcherSize : Nat := 64

/-- Byte offset of a handler's `JUMPDEST` in the linked runtime image. -/
def classicalEntryOffset (handlers : ClassicalHandlers) :
    ClassicalEntry → Nat
  | .player => classicalDispatcherSize
  | .reveal =>
      classicalDispatcherSize + handlers.blockSize .player
  | .sampleRequest =>
      classicalDispatcherSize + handlers.blockSize .player +
        handlers.blockSize .reveal
  | .oracleCallback =>
      classicalDispatcherSize + handlers.blockSize .player +
        handlers.blockSize .reveal + handlers.blockSize .sampleRequest

/-- One selector comparison and conditional jump. -/
def classicalDispatchBranch (selector : Selector) (destination : Nat) :
    Assembly :=
  [ .dup ⟨0, by decide⟩,
    .push (.selector selector),
    .eq,
    .push (.nat32 destination),
    .jumpi ]

@[simp] theorem classicalDispatchBranch_byteLength
    (selector : Selector) (destination : Nat) :
    (classicalDispatchBranch selector destination).byteLength = 13 := by
  simp [classicalDispatchBranch, Assembly.byteLength,
    Instruction.byteLength]

/-- The fixed four-way selector dispatcher. -/
def classicalDispatcher (selectors : ClassicalSelectors)
    (handlers : ClassicalHandlers) : Assembly :=
  [ .push (.one (byte 0)), .calldataload,
    .push (.one (byte 224)), .shr ] ++
  classicalDispatchBranch selectors.player
    (classicalEntryOffset handlers .player) ++
  classicalDispatchBranch selectors.reveal
    (classicalEntryOffset handlers .reveal) ++
  classicalDispatchBranch selectors.sampleRequest
    (classicalEntryOffset handlers .sampleRequest) ++
  classicalDispatchBranch selectors.oracleCallback
    (classicalEntryOffset handlers .oracleCallback) ++
  [ .pop, .push (.one (byte 0)), .push (.one (byte 0)), .revert ]

@[simp] theorem classicalDispatcher_byteLength
    (selectors : ClassicalSelectors) (handlers : ClassicalHandlers) :
    (classicalDispatcher selectors handlers).byteLength =
      classicalDispatcherSize := by
  simp only [classicalDispatcher, Assembly.byteLength_append,
    classicalDispatchBranch_byteLength]
  norm_num [Assembly.byteLength, Instruction.byteLength,
    classicalDispatcherSize]

/-- Complete linked EVM runtime assembly. -/
def classicalRuntimeAssembly (selectors : ClassicalSelectors)
    (handlers : ClassicalHandlers) : Assembly :=
  classicalDispatcher selectors handlers ++
    handlers.block .player ++
    handlers.block .reveal ++
    handlers.block .sampleRequest ++
    handlers.block .oracleCallback

/-- Total linked runtime byte length. -/
def classicalRuntimeSize (handlers : ClassicalHandlers) : Nat :=
  classicalDispatcherSize +
    handlers.blockSize .player +
    handlers.blockSize .reveal +
    handlers.blockSize .sampleRequest +
    handlers.blockSize .oracleCallback

/-- Every handler destination names a byte inside the linked runtime image. -/
theorem classicalEntryOffset_lt_runtimeSize (handlers : ClassicalHandlers)
    (entry : ClassicalEntry) :
    classicalEntryOffset handlers entry < classicalRuntimeSize handlers := by
  cases entry <;>
    simp [classicalEntryOffset, classicalRuntimeSize,
      ClassicalHandlers.blockSize]
  all_goals omega

@[simp] theorem classicalRuntimeAssembly_byteLength
    (selectors : ClassicalSelectors) (handlers : ClassicalHandlers) :
    (classicalRuntimeAssembly selectors handlers).byteLength =
      classicalRuntimeSize handlers := by
  simp [classicalRuntimeAssembly, classicalRuntimeSize]
  omega

/-- Handler code that can be linked without truncating a 32-bit destination.
The condition is intentionally stated on the complete runtime image. -/
structure LinkableHandlers where
  handlers : ClassicalHandlers
  size_fits : classicalRuntimeSize handlers < 2 ^ 32

namespace LinkableHandlers

/-- No linked jump destination is truncated by its `PUSH4` encoding. -/
theorem entryOffset_fits (handlers : LinkableHandlers)
    (entry : ClassicalEntry) :
    classicalEntryOffset handlers.handlers entry < 2 ^ 32 :=
  (classicalEntryOffset_lt_runtimeSize handlers.handlers entry).trans
    handlers.size_fits

end LinkableHandlers

/-- A linked EVM runtime image with actual bytecode and the proof that every
statically computed handler destination is represented exactly by `PUSH4`. -/
structure RuntimeImage (selectors : ClassicalSelectors) where
  handlers : LinkableHandlers
  assembly : Assembly := classicalRuntimeAssembly selectors handlers.handlers
  bytecode : List Byte := assembly.emit

namespace RuntimeImage

/-- Link independently compiled handlers behind one classical ABI. -/
def link (selectors : ClassicalSelectors) (handlers : LinkableHandlers) :
    RuntimeImage selectors where
  handlers := handlers

@[simp] theorem link_assembly (selectors : ClassicalSelectors)
    (handlers : LinkableHandlers) :
    (link selectors handlers).assembly =
      classicalRuntimeAssembly selectors handlers.handlers := by
  rfl

@[simp] theorem link_bytecode (selectors : ClassicalSelectors)
    (handlers : LinkableHandlers) :
    (link selectors handlers).bytecode =
      (classicalRuntimeAssembly selectors handlers.handlers).emit := by
  rfl

@[simp] theorem link_bytecode_length (selectors : ClassicalSelectors)
    (handlers : LinkableHandlers) :
    (link selectors handlers).bytecode.length =
      classicalRuntimeSize handlers.handlers := by
  simp [link]

end RuntimeImage

end Vegas.Machine.Contract.EVM
