/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ExprSimple
import Vegas.Machine.Contract.Storage

/-!
# EVM-sized storage words

This module supplies the first concrete finite storage representation. It does
not claim to be an EVM backend: there is no byte-level ABI, instruction IR,
gas, revert, or transaction semantics here. It only represents Boolean graph
values and completion flags by canonical 256-bit words.

The codec is available to a `simpleExpr` program exactly when all of its graph
fields and nodes have Boolean type. Other `simpleExpr` types still have total
placeholder encoding functions because `StorageCodec` is an executable
interface, but they are unsupported and no inverse law is claimed for them.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

variable {Player : Type} [DecidableEq Player]

/-- One EVM-sized word. This is a representation type, not yet an EVM value
semantics or byte encoding. -/
abbrev Word := BitVec 256

/-- Canonical Boolean encoding: false is zero and true is one. -/
def encodeBool : Bool → Word
  | false => 0
  | true => 1

/-- Decode only the two canonical Boolean words. -/
def decodeBool (word : Word) : Option Bool :=
  if word = 0 then some false
  else if word = 1 then some true
  else none

@[simp] theorem decodeBool_encodeBool (value : Bool) :
    decodeBool (encodeBool value) = some value := by
  cases value <;> simp [decodeBool, encodeBool]

/-- Total implementation used beneath the supported-type boundary. Values of
unsupported types receive a dummy word that carries no round-trip promise. -/
def encodeSimpleValue : (ty : BaseTy) → Val ty → Word
  | .int, _ => 0
  | .bool, value => encodeBool value
  | .range _ _, _ => 0
  | .option _, _ => 0

/-- Only Boolean values have a concrete decoder in this pass. -/
def decodeSimpleValue : (ty : BaseTy) → Word → Option (Val ty)
  | .int, _ => none
  | .bool, word => decodeBool word
  | .range _ _, _ => none
  | .option _, _ => none

/-- Evidence that the storage-bearing portion of a compiled program uses only
Boolean values. Payoff expressions are deliberately irrelevant here because
they are evaluated after decoding the terminal graph store. -/
structure UsesOnlyBoolStorage (program : Program Player simpleExpr) : Prop where
  field_type :
    ∀ field : Fin program.graph.fieldCount,
      (program.graph.fieldRow field).ty = .bool
  node_type :
    ∀ node : Fin program.graph.nodeCount,
      (program.graph.nodeRow node).ty = .bool

/-- A finite 256-bit storage codec for a Boolean-storage program. -/
def boolStorageCodec (program : Program Player simpleExpr)
    (usesBool : UsesOnlyBoolStorage program) : StorageCodec program where
  Word := Word
  Supported ty := ty = .bool
  encodeValue := encodeSimpleValue
  decodeValue := decodeSimpleValue
  decode_encode_value ty supported value := by
    subst ty
    exact decodeBool_encodeBool value
  field_supported := usesBool.field_type
  node_supported := usesBool.node_type
  encodeCompleted := encodeBool
  decodeCompleted := decodeBool
  decode_encode_completed := decodeBool_encodeBool

end Vegas.Machine.Contract.EVM
