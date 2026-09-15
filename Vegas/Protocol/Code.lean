/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-! # Typed logical protocol code

This module contains the public, graph-facing syntax of the ordered logical
protocol. Initial values are deliberately absent from `Code`; an ideal setup
supplies them separately through `InitialInput`. Runtime transport, raw
candidate decoding, guard verification, deadlines, and source alternatives are
not part of this syntax.
-/

namespace Vegas.Protocol

open Vegas.EventGraph

variable (Player : Type) (L : IExpr)

/-- Public metadata for one initial field. Its value belongs to setup, not
public protocol code. -/
structure InitialField where
  ty : L.Ty
  owner : Option Player

/-- One retained logical operation. The output type is part of the operation,
so a code sequence may be heterogeneous. -/
inductive Operation where
  | chance (dist : EventDist L)
  | commit (owner : Player) (guard : EventGuard L)
  | reveal (source : FieldRef L)

namespace Operation

/-- Output type of a logical operation. -/
def ty : Operation Player L → L.Ty
  | .chance dist => dist.ty
  | .commit _ guard => guard.ty
  | .reveal source => source.ty

/-- Logical operations controlled by the protocol publish public outputs.
Commit outputs remain sealed to their owner. -/
def owner : Operation Player L → Option Player
  | .chance _ | .reveal _ => none
  | .commit owner _ => some owner

/-- Precisely the graph fields whose materialized values an operation reads.
An adapter may erase the typed references to numeric runtime fields only after
establishing the corresponding tag checks. -/
def reads : Operation Player L → Finset (FieldRef L)
  | .chance dist => dist.reads
  | .commit _ guard => guard.choiceReads
  | .reveal source => {source}

end Operation

/-- Public typed protocol code. This structure contains no initial values. -/
structure Code where
  initial : List (InitialField Player L)
  operations : List (Operation Player L)

namespace Code

/-- Origin of a field in the public layout. Indices use their respective
initial-field or operation coordinate, not a compressed value list. -/
inductive FieldOrigin where
  | initial (index : Nat)
  | operation (index : Nat)
  deriving DecidableEq

/-- Numeric field assigned to an initial slot. -/
def fieldIdOfInitial (_code : Code Player L) (index : Nat) : Nat := index

/-- Numeric field assigned to an operation result. -/
def fieldIdOfOperation (code : Code Player L) (index : Nat) : Nat :=
  code.initial.length + index

/-- Classify a valid numeric field into the graph's two field regions. -/
def classifyField? (code : Code Player L) (field : Nat) : Option FieldOrigin :=
  if field < code.initial.length then
    some (.initial field)
  else
    let index := field - code.initial.length
    if index < code.operations.length then some (.operation index) else none

@[simp] theorem classifyField?_initial (code : Code Player L) (index : Nat)
    (hindex : index < code.initial.length) :
    classifyField? Player L code (fieldIdOfInitial Player L code index) =
      some (FieldOrigin.initial index) := by
  simp [classifyField?, fieldIdOfInitial, hindex]

@[simp] theorem classifyField?_operation (code : Code Player L) (index : Nat)
    (hindex : index < code.operations.length) :
    classifyField? Player L code (fieldIdOfOperation Player L code index) =
      some (FieldOrigin.operation index) := by
  simp [classifyField?, fieldIdOfOperation, hindex]

/-- Heterogeneous ideal setup input for public code. -/
abbrev InitialInput (code : Code Player L) :=
  (slot : Fin code.initial.length) → L.Val (code.initial.get slot).ty

/-- Package the value at an operation position using the existing dynamic
value carrier used by event-graph stores and runtime adapters. -/
def typedValue (code : Code Player L) (slot : Fin code.operations.length)
    (value : L.Val (code.operations.get slot).ty) : TypedValue L :=
  ⟨(code.operations.get slot).ty, value⟩

end Code

end Vegas.Protocol
