/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.SimpleEVMExpr
import Vegas.Machine.Contract.EVMExecution

/-!
# Execution correctness of Boolean EVM expressions

This module proves the stack semantics of the straight-line Boolean expression
instructions. The final compiler theorem is compositional in the code used for
variables, so calldata-backed guards and storage-backed distributions can
instantiate the same result.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

@[simp] theorem boolWord_encodeBool_eq (left right : Bool) :
    boolWord (encodeBool left = encodeBool right) =
      encodeBool (decide (left = right)) := by
  cases left <;> cases right <;> rfl

@[simp] theorem encodeBool_and (left right : Bool) :
    encodeBool left &&& encodeBool right = encodeBool (left && right) := by
  cases left <;> cases right <;> rfl

@[simp] theorem boolWord_encodeBool_iszero (value : Bool) :
    boolWord (encodeBool value = 0) = encodeBool (!value) := by
  cases value <;> rfl

/-- Stable facts about the dynamic EVM environment and storage on which an
expression's variable loads may rely. -/
abbrev BoolExprPrecondition := ExecutionEnv → TotalStorage → Prop

/-- Semantic contract of compiled Boolean expression code: under a stable read
precondition and over an arbitrary stack suffix, it pushes exactly one
canonical result and otherwise changes only the byte program counter. -/
def BoolExprCorrect (pre : BoolExprPrecondition)
    (value : Bool) (code : Assembly) : Prop :=
  ∀ (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
      (rest : List Word),
    pre env state.storage →
    state.exit = none →
    state.stack = rest →
    Assembly.CodeAt whole code state.pc →
    run code.length whole env state =
      { state with
        pc := state.pc + code.byteLength
        stack := encodeBool value :: rest }

/-- A compiled Boolean literal pushes its canonical word. -/
theorem run_pushBool (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (value : Bool) (rest : List Word)
    (hrunning : state.exit = none) (hstack : state.stack = rest)
    (hcode : Assembly.CodeAt whole
      [.push (.one (byte (if value then 1 else 0)))] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 2
        stack := encodeBool value :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  cases value <;>
    simp [run, stepInstruction, advance, hstack, Instruction.byteLength,
      encodeBool]

/-- Boolean equality consumes two canonical operands and pushes its canonical
result. -/
theorem run_eqBool (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (left right : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = encodeBool right :: encodeBool left :: rest)
    (hcode : Assembly.CodeAt whole [.eq] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := encodeBool (decide (left = right)) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  cases left <;> cases right <;>
    simp [run, stepInstruction, advance, hstack, boolWord,
      Instruction.byteLength, encodeBool]

/-- Boolean conjunction consumes two canonical operands and pushes its
canonical result. -/
theorem run_andBool (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (left right : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = encodeBool right :: encodeBool left :: rest)
    (hcode : Assembly.CodeAt whole [.and] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := encodeBool (left && right) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  simp [run, stepInstruction, advance, hstack, Instruction.byteLength]

/-- `ISZERO` implements Boolean negation on canonical operands. -/
theorem run_notBool (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (value : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = encodeBool value :: rest)
    (hcode : Assembly.CodeAt whole [.iszero] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := encodeBool (!value) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  cases value <;>
    simp [run, stepInstruction, advance, hstack, boolWord,
      Instruction.byteLength, encodeBool]

/-- The branchless selection circuit implements Boolean conditional choice and
removes all three input words. -/
theorem run_boolSelect (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (condition yes no : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack =
      encodeBool yes :: encodeBool no :: encodeBool condition :: rest)
    (hcode : Assembly.CodeAt whole boolSelectAssembly state.pc) :
    run boolSelectAssembly.length whole env state =
      { state with
        pc := state.pc + boolSelectAssembly.byteLength
        stack := encodeBool (if condition then yes else no) :: rest } := by
  apply StraightRun.run_eq ?_ hcode
  cases condition <;> cases yes <;> cases no <;>
    simp [StraightRun, boolSelectAssembly, stepInstruction, advance, hstack,
      hrunning, Assembly.byteLength, Instruction.byteLength, encodeBool]

/-- A fixed calldata load implements one Boolean variable when the read
precondition supplies exact key representation and the expected canonical
word. -/
theorem loadCalldataWord_correct (pre : BoolExprPrecondition)
    (offset : Nat) (value : Bool)
    (hread : ∀ env storage, pre env storage →
      offset < 2 ^ 256 ∧
      calldataLoad env.calldata offset = encodeBool value) :
    BoolExprCorrect pre value (loadCalldataWord offset) := by
  intro whole env state rest hpre hrunning hstack hcode
  rcases hread env state.storage hpre with ⟨hoffset, hload⟩
  have hkey : (PushData.nat256 offset).value.toNat = offset :=
    PushData.nat256_value_toNat_of_lt hoffset
  apply StraightRun.run_eq ?_ hcode
  simp only [loadCalldataWord, StraightRun]
  rw [hrunning]
  simp only [stepInstruction, advance]
  rw [hstack, hkey, hload]
  simp [Assembly.byteLength, Instruction.byteLength, hrunning]

/-- A fixed total-storage load implements one Boolean variable under the
corresponding canonical-cell precondition. -/
theorem loadStorageWord_correct (pre : BoolExprPrecondition)
    (slot : Nat) (value : Bool)
    (hread : ∀ env storage, pre env storage →
      slot < 2 ^ 256 ∧ storage slot = encodeBool value) :
    BoolExprCorrect pre value (loadStorageWord slot) := by
  intro whole env state rest hpre hrunning hstack hcode
  rcases hread env state.storage hpre with ⟨hslot, hload⟩
  have hkey : (PushData.nat256 slot).value.toNat = slot :=
    PushData.nat256_value_toNat_of_lt hslot
  apply StraightRun.run_eq ?_ hcode
  simp only [loadStorageWord, StraightRun]
  rw [hrunning]
  simp only [stepInstruction, advance]
  rw [hstack, hkey, hload]
  simp [Assembly.byteLength, Instruction.byteLength, hrunning]

theorem BoolExprCorrect.literal (pre : BoolExprPrecondition) (value : Bool) :
    BoolExprCorrect pre value
      [.push (.one (byte (if value then 1 else 0)))] := by
  intro whole env state rest _hpre hrunning hstack hcode
  exact run_pushBool whole env state value rest hrunning hstack hcode

/-- Sequential composition with EVM equality preserves expression
correctness. -/
theorem BoolExprCorrect.eq {pre : BoolExprPrecondition}
    {left right : Bool} {leftCode rightCode : Assembly}
    (hleft : BoolExprCorrect pre left leftCode)
    (hright : BoolExprCorrect pre right rightCode) :
    BoolExprCorrect pre (decide (left = right))
      (leftCode ++ rightCode ++ [.eq]) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hcode' : Assembly.CodeAt whole
      (leftCode ++ (rightCode ++ [.eq])) state.pc := by
    simpa [List.append_assoc] using hcode
  have hleftCode := hcode'.left
  have htailCode := hcode'.right
  let afterLeft : ExecutionState :=
    { state with
      pc := state.pc + leftCode.byteLength
      stack := encodeBool left :: rest }
  have hrunLeft : run leftCode.length whole env state = afterLeft := by
    simpa [afterLeft] using
      hleft whole env state rest hpre hrunning hstack hleftCode
  have hafterLeftRunning : afterLeft.exit = none := by
    simp [afterLeft, hrunning]
  have hafterLeftPre : pre env afterLeft.storage := by
    simpa [afterLeft] using hpre
  have hrightCode : Assembly.CodeAt whole rightCode afterLeft.pc := by
    have := htailCode.left
    simpa [afterLeft] using this
  let afterRight : ExecutionState :=
    { afterLeft with
      pc := afterLeft.pc + rightCode.byteLength
      stack := encodeBool right :: encodeBool left :: rest }
  have hrunRight :
      run rightCode.length whole env afterLeft = afterRight := by
    apply hright whole env afterLeft (encodeBool left :: rest) hafterLeftPre
    · exact hafterLeftRunning
    · simp [afterLeft]
    · exact hrightCode
  have hafterRightRunning : afterRight.exit = none := by
    simp [afterRight, afterLeft, hrunning]
  have heqCode : Assembly.CodeAt whole [.eq] afterRight.pc := by
    have := htailCode.right
    simpa [afterRight, afterLeft] using this
  have hrunEq : run 1 whole env afterRight =
      { afterRight with
        pc := afterRight.pc + 1
        stack := encodeBool (decide (left = right)) :: rest } := by
    apply run_eqBool whole env afterRight left right rest
      hafterRightRunning
    · simp [afterRight]
    · exact heqCode
  have hlength :
      (leftCode ++ rightCode ++ [Instruction.eq]).length =
      leftCode.length + (rightCode.length + 1) := by simp
  rw [hlength,
    run_add, hrunLeft, run_add, hrunRight, hrunEq]
  simp [afterRight, afterLeft, Assembly.byteLength, Instruction.byteLength]
  omega

/-- Sequential composition with bitwise `AND` preserves expression
correctness for canonical Boolean words. -/
theorem BoolExprCorrect.and {pre : BoolExprPrecondition} {left right : Bool}
    {leftCode rightCode : Assembly}
    (hleft : BoolExprCorrect pre left leftCode)
    (hright : BoolExprCorrect pre right rightCode) :
    BoolExprCorrect pre (left && right)
      (leftCode ++ rightCode ++ [.and]) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hcode' : Assembly.CodeAt whole
      (leftCode ++ (rightCode ++ [.and])) state.pc := by
    simpa [List.append_assoc] using hcode
  have hleftCode := hcode'.left
  have htailCode := hcode'.right
  let afterLeft : ExecutionState :=
    { state with
      pc := state.pc + leftCode.byteLength
      stack := encodeBool left :: rest }
  have hrunLeft : run leftCode.length whole env state = afterLeft := by
    simpa [afterLeft] using
      hleft whole env state rest hpre hrunning hstack hleftCode
  have hafterLeftRunning : afterLeft.exit = none := by
    simp [afterLeft, hrunning]
  have hafterLeftPre : pre env afterLeft.storage := by
    simpa [afterLeft] using hpre
  have hrightCode : Assembly.CodeAt whole rightCode afterLeft.pc := by
    have := htailCode.left
    simpa [afterLeft] using this
  let afterRight : ExecutionState :=
    { afterLeft with
      pc := afterLeft.pc + rightCode.byteLength
      stack := encodeBool right :: encodeBool left :: rest }
  have hrunRight :
      run rightCode.length whole env afterLeft = afterRight := by
    apply hright whole env afterLeft (encodeBool left :: rest) hafterLeftPre
    · exact hafterLeftRunning
    · simp [afterLeft]
    · exact hrightCode
  have hafterRightRunning : afterRight.exit = none := by
    simp [afterRight, afterLeft, hrunning]
  have handCode : Assembly.CodeAt whole [.and] afterRight.pc := by
    have := htailCode.right
    simpa [afterRight, afterLeft] using this
  have hrunAnd : run 1 whole env afterRight =
      { afterRight with
        pc := afterRight.pc + 1
        stack := encodeBool (left && right) :: rest } := by
    apply run_andBool whole env afterRight left right rest
      hafterRightRunning
    · simp [afterRight]
    · exact handCode
  have hlength :
      (leftCode ++ rightCode ++ [Instruction.and]).length =
      leftCode.length + (rightCode.length + 1) := by simp
  rw [hlength,
    run_add, hrunLeft, run_add, hrunRight, hrunAnd]
  simp [afterRight, afterLeft, Assembly.byteLength, Instruction.byteLength]
  omega

/-- Sequential composition with `ISZERO` preserves expression correctness. -/
theorem BoolExprCorrect.not {pre : BoolExprPrecondition}
    {value : Bool} {code : Assembly}
    (hcodeCorrect : BoolExprCorrect pre value code) :
    BoolExprCorrect pre (!value) (code ++ [.iszero]) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hexprCode := hcode.left
  have hnotCode := hcode.right
  let after : ExecutionState :=
    { state with
      pc := state.pc + code.byteLength
      stack := encodeBool value :: rest }
  have hrunExpr : run code.length whole env state = after := by
    simpa [after] using
      hcodeCorrect whole env state rest hpre hrunning hstack hexprCode
  have hafterRunning : after.exit = none := by
    simp [after, hrunning]
  have hnotCode' : Assembly.CodeAt whole [.iszero] after.pc := by
    simpa [after] using hnotCode
  have hrunNot := run_notBool whole env after value rest hafterRunning
    (by simp [after]) hnotCode'
  have hlength : (code ++ [Instruction.iszero]).length =
      code.length + 1 := by simp
  rw [hlength, run_add, hrunExpr, hrunNot]
  simp [after, Assembly.byteLength, Instruction.byteLength]
  omega

/-- Sequential composition with the branchless selection circuit preserves
expression correctness. -/
theorem BoolExprCorrect.select {pre : BoolExprPrecondition}
    {condition yes no : Bool}
    {conditionCode noCode yesCode : Assembly}
    (hcondition : BoolExprCorrect pre condition conditionCode)
    (hno : BoolExprCorrect pre no noCode)
    (hyes : BoolExprCorrect pre yes yesCode) :
    BoolExprCorrect pre (if condition then yes else no)
      (conditionCode ++ noCode ++ yesCode ++ boolSelectAssembly) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hcode' : Assembly.CodeAt whole
      (conditionCode ++ (noCode ++ (yesCode ++ boolSelectAssembly)))
      state.pc := by
    simpa [List.append_assoc] using hcode
  have hconditionCode := hcode'.left
  have htail1 := hcode'.right
  let afterCondition : ExecutionState :=
    { state with
      pc := state.pc + conditionCode.byteLength
      stack := encodeBool condition :: rest }
  have hrunCondition :
      run conditionCode.length whole env state = afterCondition := by
    simpa [afterCondition] using
      hcondition whole env state rest hpre hrunning hstack hconditionCode
  have hconditionRunning : afterCondition.exit = none := by
    simp [afterCondition, hrunning]
  have hconditionPre : pre env afterCondition.storage := by
    simpa [afterCondition] using hpre
  have hnoCode : Assembly.CodeAt whole noCode afterCondition.pc := by
    have := htail1.left
    simpa [afterCondition] using this
  let afterNo : ExecutionState :=
    { afterCondition with
      pc := afterCondition.pc + noCode.byteLength
      stack := encodeBool no :: encodeBool condition :: rest }
  have hrunNo : run noCode.length whole env afterCondition = afterNo := by
    apply hno whole env afterCondition (encodeBool condition :: rest)
      hconditionPre
    · exact hconditionRunning
    · simp [afterCondition]
    · exact hnoCode
  have hnoRunning : afterNo.exit = none := by
    simp [afterNo, afterCondition, hrunning]
  have hnoPre : pre env afterNo.storage := by
    simpa [afterNo, afterCondition] using hpre
  have htail2 := htail1.right
  have hyesCode : Assembly.CodeAt whole yesCode afterNo.pc := by
    have := htail2.left
    simpa [afterNo, afterCondition] using this
  let afterYes : ExecutionState :=
    { afterNo with
      pc := afterNo.pc + yesCode.byteLength
      stack := encodeBool yes :: encodeBool no :: encodeBool condition :: rest }
  have hrunYes : run yesCode.length whole env afterNo = afterYes := by
    apply hyes whole env afterNo
      (encodeBool no :: encodeBool condition :: rest)
      hnoPre
    · exact hnoRunning
    · simp [afterNo]
    · exact hyesCode
  have hyesRunning : afterYes.exit = none := by
    simp [afterYes, afterNo, afterCondition, hrunning]
  have hselectCode :
      Assembly.CodeAt whole boolSelectAssembly afterYes.pc := by
    have := htail2.right
    simpa [afterYes, afterNo, afterCondition] using this
  have hrunSelect := run_boolSelect whole env afterYes condition yes no rest
    hyesRunning (by simp [afterYes]) hselectCode
  have hlength :
      (conditionCode ++ noCode ++ yesCode ++ boolSelectAssembly).length =
      conditionCode.length +
        (noCode.length + (yesCode.length + boolSelectAssembly.length)) := by
    simp
  rw [hlength, run_add, hrunCondition, run_add, hrunNo, run_add, hrunYes,
    hrunSelect]
  simp [afterYes, afterNo, afterCondition, Assembly.byteLength]
  omega

/-- Total code generation for the accepted Boolean IR preserves its pure
meaning. -/
theorem BoolExprIR.compile_correct
    {Γ : CtxSimple}
    (pre : BoolExprPrecondition)
    (variableCode :
      {name : VarId} → HasVar Γ name .bool → Assembly)
    (ρ : PlainEnv Γ)
    (hvariable : ∀ {name : VarId} (binding : HasVar Γ name .bool),
      BoolExprCorrect pre (ρ.get binding) (variableCode binding))
    (expr : BoolExprIR Γ) :
    BoolExprCorrect pre (expr.eval ρ) (expr.compile variableCode) := by
  induction expr with
  | «variable» name binding => exact hvariable binding
  | literal value => exact BoolExprCorrect.literal pre value
  | equal left right ihLeft ihRight =>
      exact BoolExprCorrect.eq ihLeft ihRight
  | conjunction left right ihLeft ihRight =>
      exact BoolExprCorrect.and ihLeft ihRight
  | negation expression ih => exact BoolExprCorrect.not ih
  | select condition yes no ihCondition ihYes ihNo =>
      exact BoolExprCorrect.select ihCondition ihNo ihYes

/-- Every successfully compiled Boolean expression executes to the exact source
value, assuming the caller-supplied variable fragments implement the supplied
typed environment. Unsupported source constructors cannot satisfy the compile
hypothesis. -/
theorem compileBoolExpr?_correct
    {Γ : CtxSimple}
    (pre : BoolExprPrecondition)
    (variableCode :
      {name : VarId} → HasVar Γ name .bool → Assembly)
    (ρ : PlainEnv Γ)
    (hvariable : ∀ {name : VarId} (binding : HasVar Γ name .bool),
      BoolExprCorrect pre (ρ.get binding) (variableCode binding))
    (expr : Expr Γ .bool) (code : Assembly)
    (hcompile : compileBoolExpr? variableCode expr = some code) :
    BoolExprCorrect pre (evalExpr expr ρ) code := by
  cases hlower : lowerBoolExpr? expr with
  | none => simp [compileBoolExpr?, hlower] at hcompile
  | some lowered =>
      simp only [compileBoolExpr?, hlower, Option.map_some,
        Option.some.injEq] at hcompile
      subst code
      rw [← lowered.eval_eq ρ]
      exact BoolExprIR.compile_correct pre variableCode ρ hvariable lowered.ir

/-- Concrete dynamic read invariant for one retained commit guard. The head
environment binding is the proposed action calldata word; every tail binding
is its assigned graph storage cell. -/
def simpleGuardReadPrecondition (code : GuardCode simpleExpr .bool)
    (ρ : PlainEnv ((code.actionName, .bool) :: code.Context)) :
    BoolExprPrecondition :=
  fun env storage =>
    calldataLoad env.calldata 68 = encodeBool (ρ.get .here) ∧
    ∀ {name : VarId} (binding : HasVar code.Context name .bool),
      code.fieldOf binding < 2 ^ 256 ∧
      storage (code.fieldOf binding) = encodeBool (ρ.get (.there binding))

/-- The concrete guard-variable adapter implements its corresponding typed
environment lookup under the guard read invariant. -/
theorem simpleGuardVariableCode_correct
    (code : GuardCode simpleExpr .bool)
    (ρ : PlainEnv ((code.actionName, .bool) :: code.Context))
    {name : VarId}
    (binding : HasVar ((code.actionName, .bool) :: code.Context) name .bool) :
    BoolExprCorrect (simpleGuardReadPrecondition code ρ) (ρ.get binding)
      (simpleGuardVariableCode code binding) := by
  cases binding with
  | here =>
      apply loadCalldataWord_correct _ 68 (ρ.get .here)
      intro env storage hpre
      exact ⟨by norm_num, hpre.1⟩
  | there stored =>
      apply loadStorageWord_correct _ (code.fieldOf stored)
        (ρ.get (.there stored))
      intro env storage hpre
      exact hpre.2 stored

/-- Successful retained-guard compilation pushes exactly the guard's source
Boolean value for every execution satisfying its calldata/storage read
invariant. -/
theorem compileSimpleGuardCode?_correct
    (code : GuardCode simpleExpr .bool)
    (ρ : PlainEnv ((code.actionName, .bool) :: code.Context))
    (assembly : Assembly)
    (hcompile : compileSimpleGuardCode? code = some assembly) :
    BoolExprCorrect (simpleGuardReadPrecondition code ρ)
      (evalExpr code.expr ρ) assembly := by
  exact compileBoolExpr?_correct (simpleGuardReadPrecondition code ρ)
    (simpleGuardVariableCode code) ρ
    (simpleGuardVariableCode_correct code ρ) code.expr assembly hcompile

end

end Vegas.Machine.Contract.EVM
