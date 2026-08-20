/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.SimpleEVMAction

/-!
# Complete Boolean no-sample EVM handlers

This backend closes handler generation for Boolean-storage programs without
sample nodes. It validates exact calldata lengths, routes canonical node words,
compiles every player commit and permissionless reveal body, and rejects the
two unreachable oracle entry points. The result is symbolic local assembly
ready for the proved resolver and bytecode linker.

The no-sample restriction is semantic, not an implementation shortcut:
sample request/callback effects require a concrete outbound-oracle action
mechanism and retained-table realization, supplied by a later backend.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {program : Program Player simpleExpr}

/-- Evidence that the program has no stochastic graph nodes. -/
def HasNoSampleNodes (program : Program Player simpleExpr) : Prop :=
  ∀ node : Fin program.graph.nodeCount,
    match (program.graph.nodeRow node).sem with
    | .sample _ => False
    | .commit _ _ | .reveal _ => True

/-- Stable plans assigned to one classical entry point. -/
def actionsForRoute (program : Program Player simpleExpr)
    (route : ClassicalRoute) : List (ClassicalActionIR program) :=
  (compileClassicalIR program).actions.filter fun action =>
    action.route = route

/-- Exact calldata-size assertion. -/
def compileCalldataSizeEq (expected : Nat) (reject : LocalLabel) :
    LocalAssembly :=
  [ .op .calldatasize,
    .op (.push (.nat256 expected)),
    .op .eq,
    .op .iszero,
    .jumpi reject ]

/-- Route one canonical node word to its action label. -/
def compileNodeRoute (nodeOffset : Nat) (node : Nat)
    (target : LocalLabel) : LocalAssembly :=
  loadCalldataWord nodeOffset ++
    [ .op (.push (.nat256 node)),
      .op .eq,
      .jumpi target ]

/-- Compile all node comparisons in stable action order. -/
def compileNodeRoutes (nodeOffset : Nat)
    (actions : List (ClassicalActionIR program)) : LocalAssembly :=
  actions.flatMap fun action =>
    compileNodeRoute nodeOffset action.node (action.node + 1)

/-- Compile completing action blocks while threading fresh expression labels.
-/
def compileCompletingBlocks?
    (reject : LocalLabel)
    (realize : ClassicalActionIR program → Nat → Option BoolExprCode) :
    List (ClassicalActionIR program) → Nat →
      Option (LocalAssembly × Nat)
  | [], next => some ([], next)
  | action :: rest, next =>
      match realize action next with
      | none => none
      | some realized =>
          match compileCompletingBlocks? reject realize rest
              realized.nextLabel with
          | none => none
          | some (suffix, finalLabel) =>
              some
                ([.label (action.node + 1)] ++
                    compileClassicalStorageChecks reject action.checks ++
                    realized.code ++ compileClassicalActionWrites action ++
                    [.op .stop] ++ suffix,
                  finalLabel)

/-- Common exact-size/node-routing wrapper for completing calls. -/
def compileCompletingHandler?
    (calldataSize nodeOffset : Nat)
    (actions : List (ClassicalActionIR program))
    (realize : ClassicalActionIR program → Nat → Option BoolExprCode) :
    Option LocalAssembly :=
  let reject := 0
  let firstBodyLabel := program.graph.nodeCount + 1
  match compileCompletingBlocks? reject realize actions firstBodyLabel with
  | none => none
  | some (blocks, _next) =>
      some <|
        compileCalldataSizeEq calldataSize reject ++
          compileNodeRoutes nodeOffset actions ++ [.jump reject] ++
          blocks ++ classicalRejectBlock reject

/-- Complete player handler for the supported Boolean fragment. -/
def compileBooleanPlayerHandler?
    (usesBool : UsesOnlyBoolStorage program)
    (registry : PlayerRegistry Player Address)
    (players : WireCodec Player Word)
    (addresses : AddressCodec Address) : Option LocalAssembly :=
  compileCompletingHandler? 100 36 (actionsForRoute program .player)
    (fun action next =>
      compileSimplePlayerCommit? usesBool registry players addresses action
        0 next)

/-- Complete permissionless reveal handler for the supported Boolean fragment.
-/
def compileBooleanRevealHandler? : Option LocalAssembly :=
  compileCompletingHandler? (program := program) 36 4
    (actionsForRoute program .reveal) compileSimpleReveal?

/-- Immediate empty-data revert used for unavailable entry points. -/
def unavailableHandler : LocalAssembly :=
  [ .op (.push (.one (byte 0))),
    .op (.push (.one (byte 0))),
    .op .revert ]

/-- Compile every handler for a Boolean program with no sample nodes. Reveal
authorization is permissionless at this concrete backend; a restricted trigger
policy needs its own reified authorization compiler. -/
def compileBooleanNoSampleHandlers?
    (_noSamples : HasNoSampleNodes program)
    (usesBool : UsesOnlyBoolStorage program)
    (registry : PlayerRegistry Player Address)
    (players : WireCodec Player Word)
    (addresses : AddressCodec Address) : Option LocalClassicalHandlers :=
  match compileBooleanPlayerHandler? usesBool registry players addresses,
      compileBooleanRevealHandler? (program := program) with
  | some player, some reveal =>
      some
        { player := player
          reveal := reveal
          sampleRequest := unavailableHandler
          oracleCallback := unavailableHandler }
  | _, _ => none

end

end Vegas.Machine.Contract.EVM
