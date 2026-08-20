/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ExprSimple
import Vegas.Machine.Contract.EVMLocalAssembly

/-!
# Boolean `simpleExpr` lowering to EVM

The first concrete expression backend compiles the exact Boolean fragment
needed by Boolean-storage games: variables, constants, Boolean equality,
conjunction, negation, and conditionals. Unsupported constructors reject
explicitly. In particular, this pass does not assign modular EVM semantics to
Vegas's unbounded integers or invent a one-word encoding for options.

Variables are lowered by a caller-supplied code fragment. The graph guard
adapter reads the proposed action from the third player argument and stored
Boolean dependencies from their certified field-value cells.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

/-- Code plus the first unused label after it. -/
structure BoolExprCode where
  code : LocalAssembly
  nextLabel : Nat

/-- Load one 32-byte calldata word at a fixed byte offset. -/
def loadCalldataWord (offset : Nat) : LocalAssembly :=
  [.op (.push (.nat256 offset)), .op .calldataload]

/-- Load one total-storage word at a fixed key. -/
def loadStorageWord (slot : Nat) : LocalAssembly :=
  [.op (.push (.nat256 slot)), .op .sload]

/-- Compile the supported Boolean `simpleExpr` fragment. Label allocation is
monotone and threaded through recursive conditionals. -/
def compileBoolExpr?
    {Γ : CtxSimple}
    (variableCode :
      {name : VarId} → HasVar Γ name .bool → LocalAssembly) :
    Expr Γ .bool → Nat → Option BoolExprCode
  | .var _ binding, next =>
      some { code := variableCode binding, nextLabel := next }
  | .constBool value, next =>
      some
        { code := [.op (.push (.one (byte (if value then 1 else 0))))]
          nextLabel := next }
  | .eq (b := .bool) left right, next =>
      match compileBoolExpr? variableCode left next with
      | none => none
      | some leftCode =>
          match compileBoolExpr? variableCode right leftCode.nextLabel with
          | none => none
          | some rightCode =>
              some
                { code := leftCode.code ++ rightCode.code ++ [.op .eq]
                  nextLabel := rightCode.nextLabel }
  | .eq (b := .int) _ _, _ => none
  | .eq (b := .range _ _) _ _, _ => none
  | .eq (b := .option _) _ _, _ => none
  | .andBool left right, next =>
      match compileBoolExpr? variableCode left next with
      | none => none
      | some leftCode =>
          match compileBoolExpr? variableCode right leftCode.nextLabel with
          | none => none
          | some rightCode =>
              some
                { code := leftCode.code ++ rightCode.code ++ [.op .and]
                  nextLabel := rightCode.nextLabel }
  | .notBool expression, next =>
      match compileBoolExpr? variableCode expression next with
      | none => none
      | some compiled =>
          some
            { code := compiled.code ++ [.op .iszero]
              nextLabel := compiled.nextLabel }
  | .ite condition yes no, next =>
      let yesLabel := next
      let doneLabel := next + 1
      match compileBoolExpr? variableCode condition (next + 2) with
      | none => none
      | some conditionCode =>
          match compileBoolExpr? variableCode no conditionCode.nextLabel with
          | none => none
          | some noCode =>
              match compileBoolExpr? variableCode yes noCode.nextLabel with
              | none => none
              | some yesCode =>
                  some
                    { code := conditionCode.code ++ [.jumpi yesLabel] ++
                        noCode.code ++ [.jump doneLabel, .label yesLabel] ++
                        yesCode.code ++ [.label doneLabel]
                      nextLabel := yesCode.nextLabel }
  | _, _ => none

/-- The action word is the third player-call argument, starting at byte 68. -/
def playerActionWord : LocalAssembly := loadCalldataWord 68

/-- Resolve one Boolean guard variable to either the proposed action calldata
word or its retained graph field. -/
def simpleGuardVariableCode (code : GuardCode simpleExpr .bool)
    {name : VarId}
    (binding :
      HasVar ((code.actionName, .bool) :: code.Context) name .bool) :
    LocalAssembly :=
  match binding with
  | .here => playerActionWord
  | .there stored => loadStorageWord (code.fieldOf stored)

/-- Compile retained graph commit-guard code whose action word is Boolean.
The head binding is the proposed action; every tail binding is read from its
graph field-value cell. -/
def compileSimpleGuardCode? (code : GuardCode simpleExpr .bool) (next : Nat) :
    Option BoolExprCode :=
  compileBoolExpr?
    (simpleGuardVariableCode code)
    code.expr next

@[simp] theorem compileBoolExpr?_constBool
    {Γ : CtxSimple}
    (variableCode :
      {name : VarId} → HasVar Γ name .bool → LocalAssembly)
    (value : Bool) (next : Nat) :
    compileBoolExpr? variableCode (.constBool value) next =
      some
        { code := [.op (.push (.one (byte (if value then 1 else 0))))]
          nextLabel := next } := by
  simp [compileBoolExpr?]

end

end Vegas.Machine.Contract.EVM
