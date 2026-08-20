/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.Kuhn

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
