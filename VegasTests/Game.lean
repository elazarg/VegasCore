/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.Kuhn
import Vegas.Compile.Classical
import Vegas.Machine.Contract
import Vegas.Machine.Contract.Layout
import Vegas.Machine.Contract.ABI
import Vegas.Machine.Contract.Storage
import Vegas.Machine.Contract.Validator
import Vegas.Machine.Contract.State
import Vegas.Machine.Contract.StoredABI
import Vegas.Machine.Contract.Executor
import Vegas.Machine.Contract.StoredExecutor
import Vegas.Machine.Contract.Authentication
import Vegas.Machine.Contract.Calldata
import Vegas.Machine.Contract.InternalCalldata
import Vegas.Machine.Contract.Lifecycle
import Vegas.Machine.Contract.Configured
import Vegas.Machine.Contract.Wire
import Vegas.Machine.Contract.EVMWord
import Vegas.Machine.Contract.Blockchain
import Vegas.Machine.Contract.EVMCalldata
import Vegas.Machine.Contract.EVMBytes
import Vegas.Machine.Contract.Entropy
import Vegas.Machine.Contract.Imperative
import Vegas.Machine.Contract.Gas
import Vegas.Machine.Contract.Transaction

namespace VegasTests

open Vegas

abbrev TestPlayer := Fin 2

def fairCoin : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

example : fairCoin.denote.prob true = 1 / 2 := by
  unfold fairCoin
  rw [RationalLaw.prob_denote]
  dsimp
  rw [Fin.sum_univ_two]
  norm_num

example :
    simpleExpr.evalLaw
        (DistExpr.weighted (Γ := []) (b := .bool) fairCoin)
        (Env.empty Val) = fairCoin := rfl

noncomputable def coinCore : VegasCore TestPlayer simpleExpr [] :=
  .sample 0 (DistExpr.weighted (b := .bool) fairCoin)
    (.ret
      [ (0,
          Expr.ite (.var 0 .here) (.constInt 1) (.constInt (-1))),
        (1,
          Expr.ite (.var 0 .here) (.constInt (-1)) (.constInt 1)) ])

noncomputable def coinProgram : WFProgram TestPlayer simpleExpr where
  core :=
    { Γ := []
      prog := coinCore
      env := VEnv.empty simpleExpr
      wctx := by simp
      fresh := by simp [coinCore, FreshBindings, Fresh] }
  reveals := by simp [coinCore, RevealComplete]
  legal := by
    unfold coinCore
    change True
    trivial

noncomputable def coinGame : Vegas.Game TestPlayer :=
  coinProgram.game

example : coinGame.arena.execution.BoundedHorizon coinGame.horizon :=
  coinGame.bounded

noncomputable example : GameTheory.UtilityGame TestPlayer :=
  coinGame.pure

noncomputable example : GameTheory.UtilityGame TestPlayer :=
  coinGame.behavioral

noncomputable example : GameTheory.UtilityGame TestPlayer :=
  coinGame.mixedPure

/-! ## Hidden simultaneous commitments -/

def matchingPenniesSame :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .bool :=
  .eq (.var 2 (.there .here)) (.var 3 .here)

def matchingPenniesLeftPayoff :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .int :=
  .ite matchingPenniesSame (.constInt 1) (.constInt (-1))

def matchingPenniesRightPayoff :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .int :=
  .ite matchingPenniesSame (.constInt (-1)) (.constInt 1)

/-- Two source-sequential commits compile to one simultaneous initial
frontier because neither choice depends on the other. -/
noncomputable def matchingPenniesCore : VegasCore TestPlayer simpleExpr [] :=
  .commit 0 0 (.constBool true)
    (.commit 1 1 (.constBool true)
      (.reveal 2 0 0 (.there .here)
        (.reveal 3 1 1 (.there .here)
          (.ret
            [ (0, matchingPenniesLeftPayoff),
              (1, matchingPenniesRightPayoff) ]))))

noncomputable def matchingPenniesProgram :
    WFProgram TestPlayer simpleExpr where
  core :=
    { Γ := []
      prog := matchingPenniesCore
      env := VEnv.empty simpleExpr
      wctx := by simp
      fresh := by simp [matchingPenniesCore, FreshBindings, Fresh] }
  reveals := by decide
  legal := by
    unfold matchingPenniesCore
    constructor
    · intro _env
      exact ⟨false, rfl⟩
    · constructor
      · intro _env
        exact ⟨false, rfl⟩
      · trivial

noncomputable def matchingPenniesMachine :
    Machine.Program TestPlayer simpleExpr :=
  Machine.compile matchingPenniesProgram

theorem matchingPenniesMachine_graph_nodeCount :
    matchingPenniesMachine.graph.nodeCount = 4 := by
  simp [matchingPenniesMachine, Machine.compile, Machine.ofCompiled,
    matchingPenniesProgram, matchingPenniesCore, ToEventGraph.compile,
    ToEventGraph.compileCore, ToEventGraph.BuildResult.graph,
    EventGraph.Graph.nodeCount]

noncomputable def matchingPenniesGame : Vegas.Game TestPlayer :=
  matchingPenniesMachine.game

noncomputable def matchingPenniesManifest :
    Machine.Contract.Manifest matchingPenniesMachine :=
  Machine.Contract.compile matchingPenniesMachine

example : matchingPenniesManifest.actions.length =
    matchingPenniesMachine.graph.nodeCount := by
  exact Machine.Contract.Manifest.compile_actions_length
    matchingPenniesMachine

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (⟨node⟩ : Machine.Contract.Action matchingPenniesMachine) ∈
      matchingPenniesManifest.actions := by
  exact Machine.Contract.Manifest.action_mem matchingPenniesMachine node

noncomputable def matchingPenniesLayout :
    Machine.Contract.Layout matchingPenniesMachine :=
  Machine.Contract.Layout.canonical matchingPenniesMachine

noncomputable def matchingPenniesImperativeIR :
    Machine.Contract.Imperative.ContractIR matchingPenniesMachine :=
  Machine.Contract.Imperative.compile matchingPenniesMachine
    matchingPenniesLayout

example : matchingPenniesImperativeIR.actions.length = 4 := by
  rw [show matchingPenniesImperativeIR.actions.length =
      matchingPenniesMachine.graph.nodeCount by
    exact Machine.Contract.Imperative.compile_actions_length
      matchingPenniesLayout]
  exact matchingPenniesMachine_graph_nodeCount

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (Machine.Contract.Imperative.compileAction
      matchingPenniesLayout node).body.length = 3 := by
  exact Machine.Contract.Imperative.compileAction_body_length
    matchingPenniesLayout node

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    Machine.Contract.Imperative.outputSlot matchingPenniesLayout node ≠
      Machine.Contract.Imperative.completionSlot
        matchingPenniesLayout node := by
  exact Machine.Contract.Imperative.outputSlot_ne_completionSlot
    matchingPenniesLayout node

example (cfg : EventGraph.Config matchingPenniesMachine.graph)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    Machine.Contract.Imperative.evaluateAll
        (Machine.Contract.Imperative.Requirement.evaluate cfg)
        (Machine.Contract.Imperative.requirements
          matchingPenniesMachine node) =
      decide (EventGraph.Ready matchingPenniesMachine.graph cfg node) :=
  Machine.Contract.Imperative.evaluateAll_requirements cfg node

example (state : matchingPenniesMachine.State)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (Machine.Contract.Imperative.runChecks
        (Machine.Contract.Imperative.StorageCheck.evaluate
          (Machine.Contract.Imperative.completionReader
            (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
            (Machine.Contract.RawStore.encodeState
              (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
              state)))
        (Machine.Contract.Imperative.compileAction
          matchingPenniesLayout node).checks).succeeded =
      decide (EventGraph.Ready matchingPenniesMachine.graph state.1 node) := by
  exact Machine.Contract.Imperative.compileAction_checks_correct
    matchingPenniesLayout state.1 _
      (Machine.Contract.Imperative.completionReader_encodeState_agrees
        (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
        state) node

example (state : matchingPenniesMachine.State)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (Machine.Contract.Gas.runChecks
        (Machine.Contract.Gas.CheckCostModel.uniform
          Machine.Contract.Imperative.StorageCheck)
        (Machine.Contract.Imperative.StorageCheck.evaluate
          (Machine.Contract.Imperative.completionReader
            (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
            (Machine.Contract.RawStore.encodeState
              (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
              state)))
        (Machine.Contract.Imperative.compileAction
          matchingPenniesLayout node).checks).succeeded =
      decide (EventGraph.Ready matchingPenniesMachine.graph state.1 node) := by
  rw [Machine.Contract.Gas.MeteredCheckResult.succeeded,
    Machine.Contract.Gas.erase_runChecks]
  exact Machine.Contract.Imperative.compileAction_checks_correct
    matchingPenniesLayout state.1 _
      (Machine.Contract.Imperative.completionReader_encodeState_agrees
        (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
        state) node

example : Function.Injective matchingPenniesLayout.address :=
  matchingPenniesLayout.injective

example
    (field : Fin matchingPenniesMachine.graph.fieldCount)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    matchingPenniesLayout.address (.value field) ≠
      matchingPenniesLayout.address (.completed node) := by
  exact Machine.Contract.Layout.value_ne_completed
    matchingPenniesMachine field node

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    (Machine.Contract.Request.decode state
      (Machine.Contract.Request.encode command)).isSome := by
  exact Machine.Contract.Request.decode_encode_isSome command

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    Machine.Contract.Request.accepts state
      (Machine.Contract.Request.encode command) = true := by
  exact Machine.Contract.Request.accepts_encode command

theorem matchingPenniesUsesOnlyBoolStorage :
    Machine.Contract.EVM.UsesOnlyBoolStorage matchingPenniesMachine := by
  constructor
  · intro field
    fin_cases field <;> rfl
  · intro node
    fin_cases node <;> rfl

noncomputable def matchingPenniesStorageCodec :
    Machine.Contract.StorageCodec matchingPenniesMachine :=
  Machine.Contract.EVM.boolStorageCodec matchingPenniesMachine
    matchingPenniesUsesOnlyBoolStorage

example : matchingPenniesStorageCodec.Word = BitVec 256 := rfl

example :
    Machine.Contract.EVM.decodeBool
        (matchingPenniesStorageCodec.encodeValue .bool true) = some true := by
  rfl

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    Machine.Contract.RawStore.readCompleted
        (Machine.Contract.Layout.canonical matchingPenniesMachine)
        matchingPenniesStorageCodec
        (Machine.Contract.initialStore matchingPenniesMachine
          matchingPenniesStorageCodec) node = some false := by
  exact Machine.Contract.readCompleted_initialStore
    matchingPenniesMachine matchingPenniesStorageCodec node

def matchingPenniesRegistry :
    Machine.Contract.PlayerRegistry TestPlayer TestPlayer where
  address := id
  injective := Function.injective_id

example (state : matchingPenniesMachine.State)
    (call : Machine.Contract.PlayerCall TestPlayer TestPlayer simpleExpr) :
    Machine.Contract.PlayerCall.acceptsStore
        (program := matchingPenniesMachine) matchingPenniesRegistry
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState matchingPenniesStorageCodec state)
        call = true ↔
      call.caller = matchingPenniesRegistry.address call.player ∧
        Machine.Contract.Request.Represents state call.request := by
  exact
    Machine.Contract.PlayerCall.acceptsStore_encodeState_eq_true_iff
      matchingPenniesRegistry matchingPenniesStorageCodec state call

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    Machine.Contract.PlayerCalldata.acceptsStore
        (program := matchingPenniesMachine) matchingPenniesRegistry
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState matchingPenniesStorageCodec state)
        (Machine.Contract.PlayerCalldata.encodeCommit
          matchingPenniesRegistry matchingPenniesStorageCodec action step) =
      true := by
  exact
    Machine.Contract.PlayerCalldata.acceptsStore_encodeState_encodeCommit
      matchingPenniesRegistry matchingPenniesStorageCodec action step

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    Machine.Contract.PlayerCalldata.executeStore?
        (program := matchingPenniesMachine) matchingPenniesRegistry
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec state)
        (Machine.Contract.PlayerCalldata.encodeCommit
          matchingPenniesRegistry matchingPenniesStorageCodec action step) =
      some ((matchingPenniesMachine.step state (.commit who action step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec)) := by
  exact
    Machine.Contract.PlayerCalldata.executeStore?_encodeState_encodeCommit
      matchingPenniesRegistry matchingPenniesStorageCodec action step

def permissionlessTriggers :
    Machine.Contract.TriggerPolicy TestPlayer :=
  Machine.Contract.TriggerPolicy.permissionless

noncomputable def matchingPenniesContract :
    Machine.Contract.ConfiguredContract matchingPenniesMachine TestPlayer where
  codec := matchingPenniesStorageCodec
  players := matchingPenniesRegistry
  triggers := permissionlessTriggers

noncomputable def matchingPenniesClassicalBackend :
    ClassicalCompiler.Backend matchingPenniesProgram TestPlayer where
  codec := matchingPenniesStorageCodec
  players := matchingPenniesRegistry
  reveals := permissionlessTriggers
  sampleRequests := permissionlessTriggers
  oracle := { address := 0 }

noncomputable def matchingPenniesClassicalContract :=
  matchingPenniesClassicalBackend.compile

example :
    matchingPenniesClassicalContract.initial =
      Machine.Contract.OracleProtocol.idleState matchingPenniesStorageCodec
        matchingPenniesMachine.init :=
  rfl

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    matchingPenniesClassicalContract.receive
        (matchingPenniesClassicalContract.encodeState state)
        (.player
          (Machine.Contract.PlayerCalldata.encodeCommit
            matchingPenniesRegistry matchingPenniesStorageCodec action step)) =
      .success (Machine.Contract.Blockchain.CallSuccess.silent
        { store := Machine.Contract.RawStore.encodeSnapshot
            matchingPenniesStorageCodec
            (EventGraph.StateSnapshot.ofConfig
              (state.1.completeNode action.node
                { ty := step.guard.ty, value := step.value }))
          pending := none }) := by
  exact matchingPenniesClassicalContract.receive_encodeState_playerCommit
    state who action step

def matchingPenniesSelectors : Machine.Contract.EVM.Selectors where
  player := 0
  internal := 1
  player_ne_internal := by decide

noncomputable def matchingPenniesMessageABI :
    Machine.Contract.EVM.MessageABI matchingPenniesMachine
      matchingPenniesContract.codec.Word where
  selectors := matchingPenniesSelectors
  players := Machine.Contract.EVM.indexWordCodec 2 (by
    norm_num [Machine.Contract.EVM.IndexFitsWord])
  nodes := Machine.Contract.EVM.nodeWordCodec matchingPenniesMachine (by
    change matchingPenniesMachine.graph.nodeCount ≤ 2 ^ 256
    rw [matchingPenniesMachine_graph_nodeCount]
    norm_num)

noncomputable def matchingPenniesArgumentWords :
    Machine.Contract.WireCodec matchingPenniesContract.codec.Word
      Machine.Contract.EVM.Word :=
  Machine.Contract.WireCodec.identity Machine.Contract.EVM.Word

example (message : matchingPenniesContract.Message) :
    matchingPenniesMessageABI.decodeBytes matchingPenniesArgumentWords
        (matchingPenniesMessageABI.encodeBytes
          matchingPenniesArgumentWords message) =
      some message := by
  exact matchingPenniesMessageABI.decodeBytes_encodeBytes
    matchingPenniesArgumentWords message

noncomputable def matchingPenniesEntropyRealization :
    Machine.Contract.Blockchain.EntropyRealization
      matchingPenniesContract.toStochasticContract :=
  Machine.Contract.Blockchain.EntropyRealization.semantic
    matchingPenniesContract.toStochasticContract

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    (store : matchingPenniesContract.Store)
    (message : matchingPenniesContract.Message) :
    (matchingPenniesEntropyRealization.entropyLaw
        chain context store message).map
        (matchingPenniesEntropyRealization.receive
          chain context store message) =
      (matchingPenniesContract.receive chain context store message).outcomeLaw :=
  matchingPenniesEntropyRealization.law chain context store message

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    (store : matchingPenniesContract.Store)
    (message : matchingPenniesContract.Message) :
    (matchingPenniesEntropyRealization.entropyLaw
        chain context store message).map
        (fun entropy =>
          Machine.Contract.Blockchain.DeterministicResult.settle store
            (matchingPenniesEntropyRealization.receive
              chain context store message entropy)) =
      (matchingPenniesContract.receive chain context store message).settledLaw
        store := by
  exact matchingPenniesEntropyRealization.settled_law
    chain context store message

example :
    matchingPenniesMessageABI.decode
        { selector := 2, arguments := [] } = none := by
  rfl

example :
    matchingPenniesMessageABI.decode
        { selector := matchingPenniesSelectors.player
          arguments := [] } = none := by
  rfl

noncomputable def matchingPenniesWireCodec :
    matchingPenniesContract.TransactionWireCodec
      matchingPenniesContract.Calldata :=
  Machine.Contract.WireCodec.identity matchingPenniesContract.Calldata

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    matchingPenniesContract.execute?
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (.player
          (Machine.Contract.PlayerCalldata.encodeCommit
            matchingPenniesContract.players matchingPenniesContract.codec
            action step)) =
      some ((matchingPenniesMachine.step state (.commit who action step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec)) := by
  exact matchingPenniesContract.execute?_encodeState_playerCommit action step

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action)
    (hsender : context.sender = matchingPenniesContract.players.address who) :
    matchingPenniesContract.receive chain context
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (.player
          (Machine.Contract.Blockchain.PlayerMessage.encodeCommit
            matchingPenniesContract.codec action step)) =
      .success (Machine.Contract.Blockchain.CallSuccess.silentLaw Empty
        ((matchingPenniesMachine.step state (.commit who action step)).map
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec))) := by
  exact matchingPenniesContract.receive_encodeState_playerCommit
    chain context action step hsender

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action)
    (hsender : context.sender = matchingPenniesContract.players.address who) :
    matchingPenniesContract.receiveEVMBytes chain
        matchingPenniesMessageABI matchingPenniesArgumentWords context
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (matchingPenniesMessageABI.encodeBytes matchingPenniesArgumentWords
          (.player
            (Machine.Contract.Blockchain.PlayerMessage.encodeCommit
              matchingPenniesContract.codec action step))) =
      .success (Machine.Contract.Blockchain.CallSuccess.silentLaw Empty
        ((matchingPenniesMachine.step state (.commit who action step)).map
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec))) := by
  rw [matchingPenniesContract.receiveEVMBytes_encode]
  exact matchingPenniesContract.receive_encodeState_playerCommit
    chain context action step hsender

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action)
    (hsender : context.sender = matchingPenniesContract.players.address who) :
    matchingPenniesContract.receiveEVMCalldata chain
        matchingPenniesMessageABI context
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (matchingPenniesMessageABI.encode
          (.player
            (Machine.Contract.Blockchain.PlayerMessage.encodeCommit
              matchingPenniesContract.codec action step))) =
      .success (Machine.Contract.Blockchain.CallSuccess.silentLaw Empty
        ((matchingPenniesMachine.step state (.commit who action step)).map
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec))) := by
  rw [matchingPenniesContract.receiveEVMCalldata_encode]
  exact matchingPenniesContract.receive_encodeState_playerCommit
    chain context action step hsender

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    matchingPenniesContract.executeWire? matchingPenniesWireCodec
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (matchingPenniesWireCodec.encode
          (.player
            (Machine.Contract.PlayerCalldata.encodeCommit
              matchingPenniesContract.players matchingPenniesContract.codec
              action step))) =
      some ((matchingPenniesMachine.step state (.commit who action step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec)) := by
  exact matchingPenniesContract.executeWire?_encodeState_playerCommit
    matchingPenniesWireCodec action step

example (state : matchingPenniesMachine.State)
    (wire : matchingPenniesContract.Calldata)
    (haccept :
      matchingPenniesContract.acceptsWire matchingPenniesWireCodec
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state) wire = true) :
    ∃ command : matchingPenniesMachine.Command state,
      matchingPenniesContract.executeWire? matchingPenniesWireCodec
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec state) wire =
        some ((matchingPenniesMachine.step state command).map
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec)) := by
  exact matchingPenniesContract.executeWire?_encodeState_of_accepts
    matchingPenniesWireCodec state wire haccept

example {state : matchingPenniesMachine.State} (caller : TestPlayer)
    (event : EventGraph.InternalEvent matchingPenniesMachine.graph)
    (step : EventGraph.InternalStep matchingPenniesMachine.graph state.1
      event) :
    Machine.Contract.InternalCalldata.executeStore?
        (program := matchingPenniesMachine) permissionlessTriggers
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec state)
        (Machine.Contract.InternalCalldata.encode caller event) =
      some ((matchingPenniesMachine.step state (.internal event step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec)) := by
  exact
    Machine.Contract.InternalCalldata.executeStore?_encodeState_encode
      permissionlessTriggers matchingPenniesStorageCodec caller event step rfl

example {state : matchingPenniesMachine.State} (caller : TestPlayer)
    (event : EventGraph.InternalEvent matchingPenniesMachine.graph)
    (step : EventGraph.InternalStep matchingPenniesMachine.graph state.1
      event) :
    matchingPenniesContract.execute?
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (.internal
          (Machine.Contract.InternalCalldata.encode caller event)) =
      some ((matchingPenniesMachine.step state (.internal event step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec)) := by
  exact matchingPenniesContract.execute?_encodeState_internal
    caller event step rfl

example (snapshot : EventGraph.StateSnapshot matchingPenniesMachine.graph) :
    Machine.Contract.RawStore.decodeSnapshot matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeSnapshot
          matchingPenniesStorageCodec snapshot) =
      some snapshot := by
  exact Machine.Contract.RawStore.decodeSnapshot_encodeSnapshot
    matchingPenniesStorageCodec snapshot

example : Function.Injective
    (Machine.Contract.RawStore.encodeState
      (program := matchingPenniesMachine) matchingPenniesStorageCodec) := by
  exact Machine.Contract.RawStore.encodeState_injective
    matchingPenniesStorageCodec

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    Machine.Contract.Request.acceptsStore
        (program := matchingPenniesMachine) matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState
          (program := matchingPenniesMachine)
          matchingPenniesStorageCodec state)
        (Machine.Contract.Request.encode command) = true := by
  rw [Machine.Contract.Request.acceptsStore_encodeState]
  exact Machine.Contract.Request.accepts_encode command

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    Machine.Contract.Request.executeConfig? state.1
        (Machine.Contract.Request.encode command) =
      some (GameTheory.Math.Probability.FinDist.map Subtype.val
        (matchingPenniesMachine.step state command)) := by
  exact Machine.Contract.Request.executeConfig?_encode_eq_map_step
    state command

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    Machine.Contract.Request.executeStore?
        (program := matchingPenniesMachine) matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState matchingPenniesStorageCodec state)
        (Machine.Contract.Request.encode command) =
      some ((matchingPenniesMachine.step state command).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec)) := by
  exact Machine.Contract.Request.executeStore?_encodeState_encode
    matchingPenniesStorageCodec state command

example (state : matchingPenniesMachine.State)
    (request : Machine.Contract.Request TestPlayer simpleExpr)
    (haccept :
      Machine.Contract.Request.acceptsStore
          (program := matchingPenniesMachine) matchingPenniesStorageCodec
          (Machine.Contract.RawStore.encodeState
            matchingPenniesStorageCodec state) request = true) :
    ∃ command : matchingPenniesMachine.Command state,
      Machine.Contract.Request.encode command = request ∧
        Machine.Contract.Request.executeStore?
            (program := matchingPenniesMachine) matchingPenniesStorageCodec
            (Machine.Contract.RawStore.encodeState
              matchingPenniesStorageCodec state) request =
          some ((matchingPenniesMachine.step state command).map
            (Machine.Contract.RawStore.encodeState
              matchingPenniesStorageCodec)) := by
  exact Machine.Contract.Request.executeStore?_encodeState_of_accepts
    matchingPenniesStorageCodec state request haccept

example
    (store : Machine.Contract.RawStore matchingPenniesStorageCodec)
    (field : Fin matchingPenniesMachine.graph.fieldCount)
    (value : simpleExpr.Val
      (matchingPenniesMachine.graph.fieldRow field).ty) :
    Machine.Contract.RawStore.readValue matchingPenniesLayout
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.writeValue matchingPenniesLayout
          matchingPenniesStorageCodec store field value) field =
      some value := by
  exact Machine.Contract.RawStore.readValue_writeValue
    matchingPenniesLayout matchingPenniesStorageCodec store field value

example
    (store : Machine.Contract.RawStore matchingPenniesStorageCodec)
    (field : Fin matchingPenniesMachine.graph.fieldCount)
    (node : Fin matchingPenniesMachine.graph.nodeCount)
    (completed : Bool) :
    Machine.Contract.RawStore.readValue matchingPenniesLayout
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.writeCompleted matchingPenniesLayout
          matchingPenniesStorageCodec store node completed) field =
      Machine.Contract.RawStore.readValue matchingPenniesLayout
        matchingPenniesStorageCodec store field := by
  exact Machine.Contract.RawStore.readValue_writeCompleted
    matchingPenniesLayout matchingPenniesStorageCodec
    store field node completed

example (state : matchingPenniesMachine.State)
    (hterminal : matchingPenniesMachine.terminal state) :
    ∃ sourceEnv :
        VEnv simpleExpr
          (ToEventGraph.compile matchingPenniesProgram.core).terminalCtx,
      EventGraph.evalPayoffs? matchingPenniesMachine.payoffs state.1.store =
        some (evalPayoffs
          (ToEventGraph.compile matchingPenniesProgram.core).sourcePayoffs
          sourceEnv) := by
  exact Machine.compile_sourcePayoffOfTerminal
    matchingPenniesProgram state hterminal

example (state : matchingPenniesMachine.State)
    (hterminal : matchingPenniesMachine.terminal state) :
    ∃ sourceEnv :
        VEnv simpleExpr
          (ToEventGraph.compile matchingPenniesProgram.core).terminalCtx,
      Machine.Contract.terminalOutcome? matchingPenniesMachine
          matchingPenniesStorageCodec
          (Machine.Contract.RawStore.encodeState
            matchingPenniesStorageCodec state) =
        some (evalPayoffs
          (ToEventGraph.compile matchingPenniesProgram.core).sourcePayoffs
          sourceEnv) := by
  exact Machine.Contract.terminalOutcome?_compile_encodeState
    matchingPenniesProgram matchingPenniesStorageCodec state hterminal

example (state : matchingPenniesMachine.State)
    (hterminal : matchingPenniesMachine.terminal state) :
    ∃ terminalEnv :
        VEnv simpleExpr
          (ToEventGraph.compile matchingPenniesProgram.core).terminalCtx,
      SmallStep.Star
        { ctx := matchingPenniesProgram.core.Γ,
          env := matchingPenniesProgram.core.env,
          cont := matchingPenniesProgram.core.prog }
        { ctx :=
            (ToEventGraph.compile matchingPenniesProgram.core).terminalCtx,
          env := terminalEnv,
          cont := .ret
            (ToEventGraph.compile matchingPenniesProgram.core).sourcePayoffs } ∧
      EventGraph.evalPayoffs? matchingPenniesMachine.payoffs state.1.store =
        some (evalPayoffs
          (ToEventGraph.compile matchingPenniesProgram.core).sourcePayoffs
          terminalEnv) := by
  exact Machine.compile_sourceStar
    matchingPenniesProgram state hterminal

noncomputable instance matchingPenniesFiniteDomains :
    FiniteDomains matchingPenniesProgram where
  context := inferInstanceAs (FiniteVCtx ([] : VCtx TestPlayer simpleExpr))
  program :=
    { proof :=
        .commit inferInstance
          (.commit inferInstance
            (.reveal inferInstance
              (.reveal inferInstance .ret))) }

example : matchingPenniesMachine.information.PerfectRecall :=
  matchingPenniesMachine.perfectRecall

noncomputable example :
    Runtime.DeviationAdequacy matchingPenniesGame.behavioral
      matchingPenniesGame.mixedPure :=
  matchingPenniesProgram.behavioralToMixedPureAdequacy

noncomputable def matchingPenniesNode0 :
    Fin matchingPenniesMachine.graph.nodeCount :=
  ⟨0, by simp [matchingPenniesMachine, Machine.compile,
    Machine.ofCompiled, matchingPenniesProgram, matchingPenniesCore,
    ToEventGraph.compile, ToEventGraph.compileCore,
    ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount]⟩

noncomputable def matchingPenniesNode1 :
    Fin matchingPenniesMachine.graph.nodeCount :=
  ⟨1, by simp [matchingPenniesMachine, Machine.compile,
    Machine.ofCompiled, matchingPenniesProgram, matchingPenniesCore,
    ToEventGraph.compile, ToEventGraph.compileCore,
    ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount]⟩

example :
    matchingPenniesMachine.graph.prereqs matchingPenniesNode0 = ∅ := by
  decide

example :
    matchingPenniesMachine.graph.prereqs matchingPenniesNode1 = ∅ := by
  decide

example : matchingPenniesGame.arena.execution.BoundedHorizon 4 := by
  rw [← show matchingPenniesMachine.graph.nodeCount = 4 by
    exact matchingPenniesMachine_graph_nodeCount]
  exact matchingPenniesGame.bounded

end VegasTests
