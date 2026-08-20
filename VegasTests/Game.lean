/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.Kuhn
import Vegas.Machine.Contract
import Vegas.Machine.Contract.Layout
import Vegas.Machine.Contract.ABI
import Vegas.Machine.Contract.Storage
import Vegas.Machine.Contract.Validator
import Vegas.Machine.Contract.State
import Vegas.Machine.Contract.StoredABI
import Vegas.Machine.Contract.Executor
import Vegas.Machine.Contract.StoredExecutor

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

noncomputable def matchingPenniesStorageCodec :
    Machine.Contract.StorageCodec simpleExpr :=
  Machine.Contract.StorageCodec.reference simpleExpr

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

theorem matchingPenniesMachine_graph_nodeCount :
    matchingPenniesMachine.graph.nodeCount = 4 := by
  simp [matchingPenniesMachine, Machine.compile, Machine.ofCompiled,
    matchingPenniesProgram, matchingPenniesCore, ToEventGraph.compile,
    ToEventGraph.compileCore, ToEventGraph.BuildResult.graph,
    EventGraph.Graph.nodeCount]

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
