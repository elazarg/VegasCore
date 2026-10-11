/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDeviationRecall

/-! # Actual focal observations in retained source configurations -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- An arbitrary focal player has its actual graph observation, even while
foreign players retain private intentions in the reconstructed configuration. -/
theorem originalConfig_playerObserve_of_empty_memory (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (focal : Player)
    (empty : memories focal = []) :
    graph.playerObserve focal (runtime.originalConfig leaks execution memories) =
      graph.playerObserve focal execution.application.config := by
  rw [runtime.originalConfig_playerObserve]
  apply PlayerObservation.ext
  · rfl
  · rfl
  · change ((graph.ownCompletions focal execution.application.config.history).map
      (runtime.reactiveOriginal leaks focal (execution.recall focal) (memories focal)
        execution.receipts)) = _
    rw [empty]
    have unchanged : ∀ completion : graph.Completion,
        runtime.reactiveOriginal leaks focal (execution.recall focal) []
          execution.receipts completion = completion := by
      intro completion
      cases node : nodeView graph completion.event <;> simp [reactiveOriginal, node]
    change ((graph.ownCompletions focal execution.application.config.history).map
      (runtime.reactiveOriginal leaks focal (execution.recall focal) []
        execution.receipts)) = graph.ownCompletions focal execution.application.config.history
    have functions : runtime.reactiveOriginal leaks focal (execution.recall focal) []
        execution.receipts = id := funext unchanged
    simp only [functions, List.map_id_fun, id_eq]

end Vegas.EventGraphRuntime
