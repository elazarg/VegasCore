/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.BooleanEVMRuntime
import Vegas.Machine.Contract.ClassicalEVMCodegenCorrect
import Vegas.Machine.Contract.SimpleEVMExprCorrect

/-!
# Execution correctness of Boolean classical EVM handlers

This layer proves the source-facing handler wrappers against the executable
EVM semantics. The proofs are compositional over resolved local assembly, so
they apply unchanged after checked four-handler linking.
-/

namespace Vegas.Machine.Contract.EVM

noncomputable section

/-- Resolved exact-calldata-size check for a concrete rejection destination.
-/
def calldataSizeEqAssembly (expected rejectDestination : Nat) : Assembly :=
  [ .calldatasize,
    .push (.nat256 expected),
    .eq,
    .iszero,
    .push (.nat32 rejectDestination),
    .jumpi ]

@[simp] theorem calldataSizeEqAssembly_byteLength
    (expected rejectDestination : Nat) :
    (calldataSizeEqAssembly expected rejectDestination).byteLength = 42 := by
  simp [calldataSizeEqAssembly, Assembly.byteLength,
    Instruction.byteLength]

/-- Local-label resolution turns the generated size assertion into its exact
concrete instruction sequence. -/
theorem resolveFrom?_compileCalldataSizeEq
    (whole : LocalAssembly) (base expected reject offset : Nat)
    (hlabel : whole.labelOffset? reject = some offset) :
    whole.resolveFrom? base (compileCalldataSizeEq expected reject) =
      some (calldataSizeEqAssembly expected (base + offset)) := by
  simp [compileCalldataSizeEq, LocalAssembly.resolveFrom?,
    LocalAssembly.resolveItem?, hlabel, calldataSizeEqAssembly]

/-- Exact-size calldata falls through the generated assertion with its stack
and all effects unchanged. The rejection destination is not inspected on this
path. -/
theorem run_calldataSizeEq_accept
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (expected rejectDestination : Nat)
    (hrunning : state.exit = none)
    (hsize : env.calldata.length = expected)
    (hcode : Assembly.CodeAt whole
      (calldataSizeEqAssembly expected rejectDestination) state.pc) :
    run 6 whole env state =
      { state with pc := state.pc + 42 } := by
  apply StraightRun.run_eq ?_ hcode
  simp [StraightRun, calldataSizeEqAssembly, stepInstruction, advance,
    hrunning, hsize, boolWord]
  norm_num [Instruction.byteLength]

/-- A word-addressable calldata value of any other size takes the generated
rejection jump without changing the caller-visible machine effects. -/
theorem run_calldataSizeEq_reject
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (expected rejectDestination : Nat)
    (hrunning : state.exit = none)
    (hexpected : expected < 2 ^ 256)
    (hcalldata : env.calldata.length < 2 ^ 256)
    (hsize : env.calldata.length ≠ expected)
    (hdestination : rejectDestination < 2 ^ 32)
    (hcode : Assembly.CodeAt whole
      (calldataSizeEqAssembly expected rejectDestination) state.pc)
    (htarget : Assembly.CodeAt whole [.jumpdest] rejectDestination) :
    run 6 whole env state =
      { state with pc := rejectDestination } := by
  let setup : Assembly :=
    [ .calldatasize,
      .push (.nat256 expected),
      .eq,
      .iszero,
      .push (.nat32 rejectDestination) ]
  let beforeJump : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := (PushData.nat32 rejectDestination).value :: 1 :: state.stack }
  have hwordNe :
      BitVec.ofNat 256 env.calldata.length ≠ BitVec.ofNat 256 expected := by
    intro heq
    have hnat := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at hnat
    rw [Nat.mod_eq_of_lt hcalldata,
      Nat.mod_eq_of_lt hexpected] at hnat
    exact hsize hnat
  have hdecomp : calldataSizeEqAssembly expected rejectDestination =
      setup ++ [.jumpi] := by
    rfl
  rw [hdecomp] at hcode
  have hsetup := hcode.left
  have hjump := hcode.right
  have hstraight : StraightRun whole env setup state beforeJump := by
    simp [StraightRun, setup, beforeJump, stepInstruction, advance,
      hrunning, hwordNe, boolWord]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length whole env state = beforeJump :=
    hstraight.run_eq hsetup
  have hbeforeRunning : beforeJump.exit = none := by
    simp [beforeJump, hrunning]
  have hjump' : Assembly.CodeAt whole [.jumpi] beforeJump.pc := by
    simpa [beforeJump] using hjump
  have hvalid : whole.validJumpDest rejectDestination = true := by
    simp [Assembly.validJumpDest, Assembly.fetch?_of_codeAt htarget]
  have hdestinationValue :
      (PushData.nat32 rejectDestination).value.toNat = rejectDestination :=
    PushData.nat32_value_toNat_of_lt hdestination
  have hrunJump : run 1 whole env beforeJump =
      { state with pc := rejectDestination } := by
    rw [run_succ_of_codeAt 0 hbeforeRunning hjump']
    simp only [run]
    change
      (if whole.validJumpDest
          (PushData.nat32 rejectDestination).value.toNat then
        { beforeJump with
          pc := (PushData.nat32 rejectDestination).value.toNat
          stack := state.stack }
       else fault beforeJump) = { state with pc := rejectDestination }
    rw [hdestinationValue, hvalid]
    simp [beforeJump]
  rw [show 6 = setup.length + 1 by simp [setup], run_add,
    hrunSetup, hrunJump]

/-- Resolved comparison for one canonical node route. -/
def nodeRouteAssembly (nodeOffset node rejectDestination : Nat) : Assembly :=
  loadCalldataWord nodeOffset ++
    [ .push (.nat256 node),
      .eq,
      .push (.nat32 rejectDestination),
      .jumpi ]

@[simp] theorem nodeRouteAssembly_byteLength
    (nodeOffset node rejectDestination : Nat) :
    (nodeRouteAssembly nodeOffset node rejectDestination).byteLength = 74 := by
  simp [nodeRouteAssembly, loadCalldataWord, Assembly.byteLength,
    Instruction.byteLength]

/-- Local-label resolution turns one generated node comparison into its
concrete absolute-jump sequence. -/
theorem resolveFrom?_compileNodeRoute
    (whole : LocalAssembly) (base nodeOffset node target offset : Nat)
    (hlabel : whole.labelOffset? target = some offset) :
    whole.resolveFrom? base (compileNodeRoute nodeOffset node target) =
      some (nodeRouteAssembly nodeOffset node (base + offset)) := by
  simp [compileNodeRoute, LocalAssembly.resolveFrom?_append,
    LocalAssembly.resolveFrom?, LocalAssembly.resolveItem?, hlabel,
    nodeRouteAssembly]

/-- A nonmatching node word falls through one generated routing comparison
without changing the stack or effects. -/
theorem run_nodeRoute_miss
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (nodeOffset node destination : Nat)
    (hrunning : state.exit = none)
    (hoffset : nodeOffset < 2 ^ 256)
    (hmiss : calldataLoad env.calldata nodeOffset ≠
      BitVec.ofNat 256 node)
    (hcode : Assembly.CodeAt whole
      (nodeRouteAssembly nodeOffset node destination) state.pc) :
    run 6 whole env state =
      { state with pc := state.pc + 74 } := by
  have hoffsetMod : nodeOffset % 2 ^ 256 = nodeOffset :=
    Nat.mod_eq_of_lt hoffset
  norm_num at hoffsetMod
  apply StraightRun.run_eq ?_ hcode
  simp [StraightRun, nodeRouteAssembly, loadCalldataWord,
    stepInstruction, advance, hrunning,
    Nat.mod_eq_of_lt hoffsetMod, hmiss, boolWord]
  norm_num [Instruction.byteLength]

/-- A matching node word takes its valid local-label destination and consumes
all routing temporaries. -/
theorem run_nodeRoute_hit
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (nodeOffset node destination : Nat)
    (hrunning : state.exit = none)
    (hoffset : nodeOffset < 2 ^ 256)
    (hload : calldataLoad env.calldata nodeOffset = BitVec.ofNat 256 node)
    (hdestination : destination < 2 ^ 32)
    (hcode : Assembly.CodeAt whole
      (nodeRouteAssembly nodeOffset node destination) state.pc)
    (htarget : Assembly.CodeAt whole [.jumpdest] destination) :
    run 6 whole env state =
      { state with pc := destination } := by
  have hoffsetMod : nodeOffset % 2 ^ 256 = nodeOffset :=
    Nat.mod_eq_of_lt hoffset
  norm_num at hoffsetMod
  let setup : Assembly :=
    loadCalldataWord nodeOffset ++
      [ .push (.nat256 node),
        .eq,
        .push (.nat32 destination) ]
  let beforeJump : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := (PushData.nat32 destination).value :: 1 :: state.stack }
  have hdecomp : nodeRouteAssembly nodeOffset node destination =
      setup ++ [.jumpi] := by
    simp [nodeRouteAssembly, setup, List.append_assoc]
  rw [hdecomp] at hcode
  have hsetup := hcode.left
  have hjump := hcode.right
  have hstraight : StraightRun whole env setup state beforeJump := by
    simp [StraightRun, setup, beforeJump, loadCalldataWord,
      stepInstruction, advance, hrunning,
      Nat.mod_eq_of_lt hoffsetMod, hload, boolWord]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length whole env state = beforeJump :=
    hstraight.run_eq hsetup
  have hbeforeRunning : beforeJump.exit = none := by
    simp [beforeJump, hrunning]
  have hjump' : Assembly.CodeAt whole [.jumpi] beforeJump.pc := by
    simpa [beforeJump] using hjump
  have hvalid : whole.validJumpDest destination = true := by
    simp [Assembly.validJumpDest, Assembly.fetch?_of_codeAt htarget]
  have hdestinationValue :
      (PushData.nat32 destination).value.toNat = destination :=
    PushData.nat32_value_toNat_of_lt hdestination
  have hrunJump : run 1 whole env beforeJump =
      { state with pc := destination } := by
    rw [run_succ_of_codeAt 0 hbeforeRunning hjump']
    simp only [run]
    change
      (if whole.validJumpDest
          (PushData.nat32 destination).value.toNat then
        { beforeJump with
          pc := (PushData.nat32 destination).value.toNat
          stack := state.stack }
       else fault beforeJump) = { state with pc := destination }
    rw [hdestinationValue, hvalid]
    simp [beforeJump]
  rw [show 6 = setup.length + 1 by simp [setup, loadCalldataWord],
    run_add, hrunSetup, hrunJump]

end

end Vegas.Machine.Contract.EVM
