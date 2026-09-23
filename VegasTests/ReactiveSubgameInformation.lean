/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMemorySubgames
import Vegas.Pending.ReactiveSubgameInformation

/-! # The private-memory obstruction applies to the Vegas reactive adapter

These instances of the generic theorem require no service or observation
assumptions. The two memory values may differ only in auxiliary private data.
-/

noncomputable section

namespace VegasTests.ReactiveSubgameInformation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (Payload graph))

example : Nontrivial (runtime.reactiveApplication leaks).Memory :=
  inferInstanceAs (Nontrivial (ResponseMemory graph))

example (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (root inside : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).History)
    (proper : InformationModel.IsSubgameRoot
      ((runtime.reactiveApplication leaks).information initial horizon scheduler) root)
    (before : (runtime.reactiveApplication leaks).Control) (rootState : root.state = some before)
    (first second : Player) (different : first ≠ second)
    (firstRecall : before.execution.recall first ≠ [])
    (secondRecall : before.execution.recall second ≠ [])
    (reached : ExecutionProtocol.HistoryReaches
      ((runtime.reactiveApplication leaks).protocol initial horizon scheduler) root inside)
    (running : ¬ ExecutionProtocol.terminal
      ((runtime.reactiveApplication leaks).protocol initial horizon scheduler) inside.state)
    (observer : Player) :
    ¬ ExecutionProtocol.active
      ((runtime.reactiveApplication leaks).protocol initial horizon scheduler)
      inside.state observer := by
  let : Nontrivial (runtime.reactiveApplication leaks).Memory :=
    inferInstanceAs (Nontrivial (ResponseMemory graph))
  exact (runtime.reactiveApplication leaks).subgameRoot_no_future_decision_of_two_responders
    initial horizon scheduler root inside proper before rootState first second different
    firstRecall secondRecall reached running observer

end VegasTests.ReactiveSubgameInformation
