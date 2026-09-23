/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeResponse
import Vegas.Pending.ResponseRecall
import GameTheoryExtensions.Protocol.ResponseSampling

/-! # Implementing a response law through native invocation policies

The player reconstructs each response entry from its own recall and conditions
the desired response law on actions already taken. One native policy handles
successive responses without an externally supplied offset or law. The endpoint
law equals drawing the response at once, including all correlations and records.
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

/-- A strategy selects a law of responses at every possible entry input. -/
abbrev ResponsePolicy (budget : NativeInput graph → Nat) :=
  (input : NativeInput graph) → FinDist (PlayerResponse graph (budget input))

/-- One policy for all native invocations. Both the entry and conditional
action prefix are reconstructed from the actual private invocation arguments. -/
def expandResponsePolicy (budget : NativeInput graph → Nat) (policy : ResponsePolicy budget) :
    NativePolicy graph := fun history view =>
  let fragment := responsePosition budget (history, view)
  ResponseSampling.next ((policy fragment.entry).map Subtype.val) fragment.actions

private theorem expandResponsePolicy_run (runtime : EventGraphRuntime graph) (who : Player)
    (budget : NativeInput graph → Nat) (policy : ResponsePolicy budget)
    (count : Nat) (execution : NativeExecution runtime) (fragment : ResponseFragment graph)
    (position : responsePosition budget (runtime.nativeInput who execution) = fragment)
    (within : fragment.actions.length + count ≤ budget fragment.entry) :
    runtime.invokeNativeFor who (expandResponsePolicy budget policy) count execution =
      (ResponseSampling.run (fun past => ResponseSampling.next
        ((policy fragment.entry).map Subtype.val) (fragment.actions ++ past)) count).map
          (runtime.takeActions who execution) := by
  induction count generalizing execution fragment with
  | zero => simp only [invokeNativeFor, ResponseSampling.run, FinDist.map_pure,
      takeActions, List.foldl_nil]
  | succ count ih =>
      have chosen : expandResponsePolicy budget policy (execution.principalHistory who)
          (runtime.nativeView execution.native who) =
          ResponseSampling.next ((policy fragment.entry).map Subtype.val) fragment.actions := by
        change ResponseSampling.next
          ((policy (responsePosition budget (runtime.nativeInput who execution)).entry).map
            Subtype.val) (responsePosition budget (runtime.nativeInput who execution)).actions = _
        rw [position]
      simp only [invokeNativeFor, invokeNative, chosen, actionStep,
        FinDist.bind_bind, FinDist.pure_bind, ResponseSampling.run, List.append_nil,
        FinDist.map_bind, FinDist.map_comp]
      apply FinDist.bind_congr
      intro action _
      cases count with
      | zero => simp only [invokeNativeFor, ResponseSampling.run, FinDist.map_pure,
          Function.comp_apply, takeActions, List.foldl_cons, List.foldl_nil]
      | succ count =>
          have unfinished : (fragment.actions ++ [action]).length < budget fragment.entry := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          rw [ih (runtime.takeAction who execution action)
            ⟨fragment.entry, fragment.actions ++ [action]⟩
            (runtime.responsePosition_takeAction who budget execution action fragment
              position unfinished) (by
                simp only [List.length_append, List.length_cons, List.length_nil]
                omega)]
          simp only [List.append_assoc, List.singleton_append]
          rfl

/-- The same playerwise policy works at every response boundary, including
off-path entries. No entry offset or response law is supplied by the service. -/
theorem expandResponsePolicy_law (runtime : EventGraphRuntime graph) (who : Player)
    (budget : NativeInput graph → Nat) (policy : ResponsePolicy budget)
    (execution : NativeExecution runtime)
    (boundary : responseRecall budget (execution.principalHistory who) = none) :
    runtime.invokeNativeFor who (expandResponsePolicy budget policy)
        (budget (runtime.nativeInput who execution)) execution =
      (policy (runtime.nativeInput who execution)).map
        (fun response => runtime.takeActions who execution response.1) := by
  rw [runtime.expandResponsePolicy_run who budget policy _ execution
    ⟨runtime.nativeInput who execution, []⟩ (by
      change (responseRecall budget (execution.principalHistory who)).getD _ = _
      rw [boundary]
      rfl) (by simp only [List.length_nil, Nat.zero_add, le_refl])]
  simp only [List.nil_append]
  rw [ResponseSampling.run_next]
  · rw [FinDist.map_comp]
    rfl
  · intro actions supported
    obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ supported
    exact response.2

end Vegas.EventGraphRuntime
