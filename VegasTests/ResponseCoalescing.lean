/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPlayerAction

/-! # Endpoint properties of uninterrupted native responses

Executing a fixed list of one player's actions retains every packet and its
order, and supplies no intermediate input to another player. The service and
wire are not invoked during the list. This experiment does not replace the
native protocol or assert an SPE theorem. Information-local sampling of the
list needs an additional own-observation lemma on reachable executions.
-/

noncomputable section

namespace VegasTests.ResponseCoalescing

open Vegas Vegas.EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}

def execute (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (actions : List (PlayerAction graph)) :
    NativeExecution runtime := actions.foldl (runtime.takeAction who) execution

/-- Future policies receive exactly the endpoint of the original actions,
including pending envelopes, sender counters, candidates, receipts, and recall. -/
theorem execute_append (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (first second : List (PlayerAction graph)) :
    execute runtime who execution (first ++ second) =
      execute runtime who (execute runtime who execution first) second := by
  exact List.foldl_append

/-- No wire or service invocation occurs inside the response. -/
theorem environment_recall (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (actions : List (PlayerAction graph)) :
    (execute runtime who execution actions).environmentHistory = execution.environmentHistory := by
  induction actions generalizing execution with
  | nil => rfl
  | cons action rest ih => exact ih (runtime.takeAction who execution action)

/-- Every other player's entire invocation input remains unchanged. -/
theorem other_input (runtime : EventGraphRuntime graph) (actor observer : Player)
    (different : observer ≠ actor) (execution : NativeExecution runtime)
    (actions : List (PlayerAction graph)) :
    let next := execute runtime actor execution actions
    (next.principalHistory observer, runtime.nativeView next.native observer) =
      (execution.principalHistory observer, runtime.nativeView execution.native observer) := by
  induction actions generalizing execution with
  | nil => rfl
  | cons action rest ih =>
      exact (ih (runtime.takeAction actor execution action)).trans
        (runtime.takeAction_other_input actor observer different execution action)

/-- Coalescing retains the private record of every constituent action. -/
theorem own_recall_length (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (actions : List (PlayerAction graph)) :
    ((execute runtime who execution actions).principalHistory who).length =
      (execution.principalHistory who).length + actions.length := by
  induction actions generalizing execution with
  | nil => simp only [execute, List.foldl_nil, List.length_nil, Nat.add_zero]
  | cons action rest ih =>
      change ((execute runtime who
        (runtime.takeAction who execution action) rest).principalHistory who).length = _
      rw [ih, runtime.takeAction_history_self]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

end VegasTests.ResponseCoalescing
