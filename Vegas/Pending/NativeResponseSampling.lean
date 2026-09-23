/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeResponse
import GameTheoryExtensions.Protocol.ResponseSampling

/-! # Implementing a response law through native invocation policies

At a response entry the player knows its own recall length and its desired
response law. A single native policy subsequently conditions that law on the
actions it has already taken. The endpoint law equals drawing the response
at once, including all correlations and private records.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def actionsSince (start : Nat) (history : List (NativeEntry graph)) : List (PlayerAction graph) :=
  (history.drop start).map NativeEntry.action

theorem actionsSince_takeAction (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (action : PlayerAction graph) (start : Nat)
    (within : start ≤ (execution.principalHistory who).length) :
    actionsSince start ((runtime.takeAction who execution action).principalHistory who) =
      actionsSince start (execution.principalHistory who) ++ [action] := by
  rw [runtime.takeAction_history_self]
  simp only [actionsSince, List.drop_append_of_le_length within, List.map_append,
    List.map_cons, List.map_nil]

/-- The entry offset and desired law are private data available when a
response starts. Subsequent choices read only the player's actual recall. -/
def sampleResponsePolicy (law : FinDist (List (PlayerAction graph))) (start : Nat) :
    NativePolicy graph := fun history _ => ResponseSampling.next law (actionsSince start history)

private theorem sampleResponsePolicy_run (runtime : EventGraphRuntime graph) (who : Player)
    (law : FinDist (List (PlayerAction graph))) (start count : Nat)
    (execution : NativeExecution runtime)
    (within : start ≤ (execution.principalHistory who).length) :
    runtime.invokeNativeFor who (sampleResponsePolicy law start) count execution =
      (ResponseSampling.run (fun past => ResponseSampling.next law
        (actionsSince start (execution.principalHistory who) ++ past)) count).map
          (runtime.takeActions who execution) := by
  induction count generalizing execution with
  | zero => simp only [invokeNativeFor, ResponseSampling.run, FinDist.map_pure,
      takeActions, List.foldl_nil]
  | succ count ih =>
      simp only [invokeNativeFor, invokeNative, sampleResponsePolicy, actionStep,
        FinDist.bind_bind, FinDist.pure_bind, ResponseSampling.run, List.append_nil,
        FinDist.map_bind, FinDist.map_comp]
      apply FinDist.bind_congr
      intro action _
      have nextWithin : start ≤
          ((runtime.takeAction who execution action).principalHistory who).length := by
        rw [runtime.takeAction_history_self, List.length_append]
        omega
      rw [ih _ nextWithin, runtime.actionsSince_takeAction who execution action start within]
      simp only [List.append_assoc, List.singleton_append]
      rfl

/-- Local realization of every response law by one information-local native
policy. The law and entry offset are uniform across equal player inputs. -/
theorem sampleResponsePolicy_law (runtime : EventGraphRuntime graph) (who : Player)
    {count : Nat} (law : FinDist (PlayerResponse graph count))
    (execution : NativeExecution runtime) :
    runtime.invokeNativeFor who
        (sampleResponsePolicy (law.map Subtype.val) (execution.principalHistory who).length)
        count execution =
      law.map (fun response => runtime.takeActions who execution response.1) := by
  rw [runtime.sampleResponsePolicy_run who _ _ _ execution (Nat.le_refl _)]
  simp only [actionsSince, List.drop_length, List.map_nil, List.nil_append]
  rw [ResponseSampling.run_next]
  · rw [FinDist.map_comp]
    rfl
  · intro actions supported
    obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ supported
    exact response.2

end Vegas.EventGraphRuntime

-- OPEN OBLIGATION: Uniform full-service response policy correspondence
-- The local law uses the response's entry offset and entry law. Recover successive
-- entries from own recall and construct one playerwise policy map for the whole
-- service, including arbitrary off-path response histories and replacements.
