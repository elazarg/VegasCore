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

Variables are lowered by a caller-supplied straight-line code fragment. The
graph guard adapter reads the proposed action from the third player argument
and stored Boolean dependencies from their certified field-value cells.

Conditionals use a canonical-Boolean selection circuit rather than dynamic
jumps. Besides simplifying executable refinement, this avoids making the
chosen pure expression branch observable through control flow.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

/-- Symbolic handler fragment plus the first unused local label. -/
structure GeneratedLocalCode where
  code : LocalAssembly
  nextLabel : Nat

/-- Load one 32-byte calldata word at a fixed byte offset. -/
def loadCalldataWord (offset : Nat) : Assembly :=
  [.push (.nat256 offset), .calldataload]

/-- Load one total-storage word at a fixed key. -/
def loadStorageWord (slot : Nat) : Assembly :=
  [.push (.nat256 slot), .sload]

/-- Select `yes` when the third stack word is one and `no` when it is zero.
Input is `yes :: no :: condition :: rest`; output is the selected canonical
Boolean word followed by `rest`. -/
def boolSelectAssembly : Assembly :=
  [ .dup ⟨1, by decide⟩,
    .xor,
    .swap ⟨1, by decide⟩,
    .swap ⟨0, by decide⟩,
    .swap ⟨1, by decide⟩,
    .and,
    .xor ]

/-- Closed Boolean-only expression IR accepted by the EVM backend. Unsupported
source constructors are eliminated before code generation. -/
inductive BoolExprIR (Γ : CtxSimple) where
  | variable (name : VarId) (binding : HasVar Γ name .bool)
  | literal (value : Bool)
  | equal (left right : BoolExprIR Γ)
  | conjunction (left right : BoolExprIR Γ)
  | negation (expression : BoolExprIR Γ)
  | select (condition yes no : BoolExprIR Γ)

namespace BoolExprIR

/-- Pure meaning of the Boolean backend IR. -/
def eval (ρ : PlainEnv Γ) : BoolExprIR Γ → Bool
  | .variable _ binding => ρ.get binding
  | .literal value => value
  | .equal left right => decide (left.eval ρ = right.eval ρ)
  | .conjunction left right => left.eval ρ && right.eval ρ
  | .negation expression => !(expression.eval ρ)
  | .select condition yes no =>
      if condition.eval ρ then yes.eval ρ else no.eval ρ

/-- Total straight-line code generation for the accepted Boolean IR. -/
def compile
    (variableCode :
      {name : VarId} → HasVar Γ name .bool → Assembly) :
    BoolExprIR Γ → Assembly
  | .variable _ binding => variableCode binding
  | .literal value => [.push (.one (byte (if value then 1 else 0)))]
  | .equal left right =>
      left.compile variableCode ++ right.compile variableCode ++ [.eq]
  | .conjunction left right =>
      left.compile variableCode ++ right.compile variableCode ++ [.and]
  | .negation expression => expression.compile variableCode ++ [.iszero]
  | .select condition yes no =>
      condition.compile variableCode ++ no.compile variableCode ++
        yes.compile variableCode ++ boolSelectAssembly

end BoolExprIR

/-- A successfully accepted source expression carries the exact semantic
connection to its Boolean-only backend IR. -/
structure LoweredBoolExpr {Γ : CtxSimple} (source : Expr Γ .bool) where
  ir : BoolExprIR Γ
  eval_eq : ∀ ρ, ir.eval ρ = evalExpr source ρ

@[ext] theorem LoweredBoolExpr.ext {source : Expr Γ .bool}
    {left right : LoweredBoolExpr source} (hir : left.ir = right.ir) :
    left = right := by
  cases left
  cases right
  cases hir
  rfl

/-- Validate and lower exactly the supported Boolean source fragment. -/
def lowerBoolExpr? {Γ : CtxSimple} :
    (source : Expr Γ .bool) → Option (LoweredBoolExpr source)
  | .var name binding =>
      some { ir := .variable name binding, eval_eq := by intro; rfl }
  | .constBool value =>
      some { ir := .literal value, eval_eq := by intro; rfl }
  | .eq (b := .bool) left right =>
      match lowerBoolExpr? left, lowerBoolExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .equal loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ]
                rfl }
      | _, _ => none
  | .eq (b := .int) _ _ => none
  | .eq (b := .range _ _) _ _ => none
  | .eq (b := .option _) _ _ => none
  | .andBool left right =>
      match lowerBoolExpr? left, lowerBoolExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .conjunction loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ] }
      | _, _ => none
  | .notBool expression =>
      match lowerBoolExpr? expression with
      | some lowered =>
          some
            { ir := .negation lowered.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr, lowered.eval_eq ρ] }
      | none => none
  | .ite condition yes no =>
      match lowerBoolExpr? condition, lowerBoolExpr? yes, lowerBoolExpr? no with
      | some loweredCondition, some loweredYes, some loweredNo =>
          some
            { ir := .select loweredCondition.ir loweredYes.ir loweredNo.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr,
                  loweredCondition.eval_eq ρ, loweredYes.eval_eq ρ,
                  loweredNo.eval_eq ρ] }
      | _, _, _ => none
  | _ => none

/-- Compile the supported Boolean `simpleExpr` fragment to straight-line EVM
assembly. -/
def compileBoolExpr?
    {Γ : CtxSimple}
    (variableCode :
      {name : VarId} → HasVar Γ name .bool → Assembly)
    (source : Expr Γ .bool) : Option Assembly :=
  (lowerBoolExpr? source).map fun lowered => lowered.ir.compile variableCode

/-- The action word is the third player-call argument, starting at byte 68. -/
def playerActionWord : Assembly := loadCalldataWord 68

/-- Resolve one Boolean guard variable to either the proposed action calldata
word or its retained graph field. -/
def simpleGuardVariableCode (code : GuardCode simpleExpr .bool)
    {name : VarId}
    (binding :
      HasVar ((code.actionName, .bool) :: code.Context) name .bool) :
    Assembly :=
  match binding with
  | .here => playerActionWord
  | .there stored => loadStorageWord (code.fieldOf stored)

/-- Compile retained graph commit-guard code whose action word is Boolean.
The head binding is the proposed action; every tail binding is read from its
graph field-value cell. -/
def compileSimpleGuardCode? (code : GuardCode simpleExpr .bool) :
    Option Assembly :=
  compileBoolExpr?
    (simpleGuardVariableCode code)
    code.expr

@[simp] theorem compileBoolExpr?_constBool
    {Γ : CtxSimple}
    (variableCode :
      {name : VarId} → HasVar Γ name .bool → Assembly)
    (value : Bool) :
    compileBoolExpr? variableCode (.constBool value) =
      some [.push (.one (byte (if value then 1 else 0)))] := by
  let lowered : LoweredBoolExpr (.constBool value) :=
    { ir := @BoolExprIR.literal Γ value
      eval_eq := by intro; simp [BoolExprIR.eval, evalExpr] }
  have hlower : lowerBoolExpr? (.constBool value) = some lowered := by
    unfold lowerBoolExpr?
    apply congrArg some
    apply LoweredBoolExpr.ext
    rfl
  simp [compileBoolExpr?, hlower, lowered, BoolExprIR.compile]

end

end Vegas.Machine.Contract.EVM
