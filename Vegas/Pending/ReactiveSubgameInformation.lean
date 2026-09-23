/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMemorySubgames
import Vegas.Pending.ReactiveRuntime

/-! # Scratch data alone suppresses foreign continuation subgames

The memory relabeling below preserves every remembered source intention.
Only the unused auxiliary data changes; commitment material and traffic stay
fixed by the generic reactive-history transformation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (Payload graph))

theorem not_subgameRoot_of_foreign_response
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (root inside : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).History)
    (before : (runtime.reactiveApplication leaks).Control) (rootState : root.state = some before)
    (owner observer : Player) (different : observer ≠ owner)
    (recalled : before.execution.recall owner ≠ [])
    (reached : ExecutionProtocol.HistoryReaches
      ((runtime.reactiveApplication leaks).protocol initial horizon scheduler) root inside)
    (running : ¬ ExecutionProtocol.terminal
      ((runtime.reactiveApplication leaks).protocol initial horizon scheduler) inside.state)
    (active : ExecutionProtocol.active
      ((runtime.reactiveApplication leaks).protocol initial horizon scheduler)
      inside.state observer) :
    ¬ InformationModel.IsSubgameRoot
      ((runtime.reactiveApplication leaks).information initial horizon scheduler) root := by
  obtain ⟨first, rest, prior⟩ := List.exists_cons_of_ne_nil recalled
  let change : ResponseMemory graph → ResponseMemory graph := fun memory =>
    { memory with privateData := first.action.memory.privateData ++ [.inl 0] }
  apply (runtime.reactiveApplication leaks).not_subgameRoot_of_memory_relabeling
    initial horizon scheduler root inside before rootState owner observer different
    first (by simp [prior]) change ?_ reached running active
  intro memory equal
  have lengths := congrArg (fun saved : ResponseMemory graph => saved.privateData.length) equal
  simp only [change, List.length_append, List.length_cons, List.length_nil] at lengths
  omega

end Vegas.EventGraphRuntime
