/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeResponse

/-! # Recovering response entries from private recall

A response capacity is a function of its entry input. Its first recorded
before-view and earlier recall therefore determine where the response ends.
Parsing those records recovers the entry of an unfinished response without
adding a memory tag, an observation, or a service cursor to player policies.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

structure ResponseFragment (graph : Vegas.EventGraph Player L) where
  entry : NativeInput graph
  actions : List (PlayerAction graph)

def ResponseFragment.advance (budget : NativeInput graph → Nat) (input : NativeInput graph)
    (fragment : Option (ResponseFragment graph)) (action : PlayerAction graph) :
    Option (ResponseFragment graph) :=
  let current := fragment.getD ⟨input, []⟩
  let actions := current.actions ++ [action]
  if actions.length < budget current.entry then some ⟨current.entry, actions⟩ else none

private def recallStep (budget : NativeInput graph → Nat)
    (state : List (NativeEntry graph) × Option (ResponseFragment graph))
    (record : NativeEntry graph) :
    List (NativeEntry graph) × Option (ResponseFragment graph) :=
  (state.1 ++ [record], ResponseFragment.advance budget (state.1, record.beforeView)
    state.2 record.action)

/-- `none` means all recalled responses are complete. Zero budgets on
impossible inputs are treated as single-record responses to keep parsing total. -/
def responseRecall (budget : NativeInput graph → Nat) (history : List (NativeEntry graph)) :
    Option (ResponseFragment graph) := (history.foldl (recallStep budget) ([], none)).2

private theorem recallStep_history (budget : NativeInput graph → Nat)
    (records : List (NativeEntry graph))
    (state : List (NativeEntry graph) × Option (ResponseFragment graph)) :
    (records.foldl (recallStep budget) state).1 = state.1 ++ records := by
  induction records generalizing state with
  | nil => simp only [List.foldl_nil, List.append_nil]
  | cons record records ih =>
      rw [List.foldl_cons, ih]
      simp only [recallStep, List.append_assoc, List.singleton_append]

theorem responseRecall_append (budget : NativeInput graph → Nat)
    (history : List (NativeEntry graph)) (record : NativeEntry graph) :
    responseRecall budget (history ++ [record]) =
      ResponseFragment.advance budget (history, record.beforeView)
        (responseRecall budget history) record.action := by
  simp only [responseRecall, List.foldl_append, List.foldl_cons, List.foldl_nil, recallStep,
    recallStep_history, List.nil_append]

def responsePosition (budget : NativeInput graph → Nat) (input : NativeInput graph) :
    ResponseFragment graph := (responseRecall budget input.1).getD ⟨input, []⟩

variable [DecidableEq Player]

theorem responseRecall_takeAction (runtime : EventGraphRuntime graph) (who : Player)
    (budget : NativeInput graph → Nat) (execution : NativeExecution runtime)
    (action : PlayerAction graph) :
    responseRecall budget ((runtime.takeAction who execution action).principalHistory who) =
      ResponseFragment.advance budget (runtime.nativeInput who execution)
        (responseRecall budget (execution.principalHistory who)) action := by
  rw [runtime.takeAction_history_self, responseRecall_append]
  rfl

theorem responseRecall_takeAction_position (runtime : EventGraphRuntime graph) (who : Player)
    (budget : NativeInput graph → Nat) (execution : NativeExecution runtime)
    (action : PlayerAction graph) (fragment : ResponseFragment graph)
    (position : responsePosition budget (runtime.nativeInput who execution) = fragment) :
    responseRecall budget ((runtime.takeAction who execution action).principalHistory who) =
      if (fragment.actions ++ [action]).length < budget fragment.entry then
        some ⟨fragment.entry, fragment.actions ++ [action]⟩ else none := by
  rw [runtime.responseRecall_takeAction]
  change (responseRecall budget (execution.principalHistory who)).getD
    ⟨runtime.nativeInput who execution, []⟩ = fragment at position
  simp only [ResponseFragment.advance, position]

theorem responsePosition_takeAction (runtime : EventGraphRuntime graph) (who : Player)
    (budget : NativeInput graph → Nat) (execution : NativeExecution runtime)
    (action : PlayerAction graph) (fragment : ResponseFragment graph)
    (position : responsePosition budget (runtime.nativeInput who execution) = fragment)
    (unfinished : (fragment.actions ++ [action]).length < budget fragment.entry) :
    responsePosition budget (runtime.nativeInput who
      (runtime.takeAction who execution action)) =
        ⟨fragment.entry, fragment.actions ++ [action]⟩ := by
  change (responseRecall budget
    ((runtime.takeAction who execution action).principalHistory who)).getD _ = _
  rw [runtime.responseRecall_takeAction_position who budget execution action fragment position]
  simp only [unfinished, ↓reduceIte, Option.getD_some]

private theorem responseRecall_finish (runtime : EventGraphRuntime graph) (who : Player)
    (budget : NativeInput graph → Nat) (execution : NativeExecution runtime)
    (actions : List (PlayerAction graph)) (fragment : ResponseFragment graph)
    (position : responsePosition budget (runtime.nativeInput who execution) = fragment)
    (nonempty : actions ≠ [])
    (length : fragment.actions.length + actions.length = budget fragment.entry) :
    responseRecall budget
      ((runtime.takeActions who execution actions).principalHistory who) = none := by
  induction actions generalizing execution fragment with
  | nil => exact (nonempty rfl).elim
  | cons action actions ih =>
      cases actions with
      | nil =>
          change responseRecall budget
            ((runtime.takeAction who execution action).principalHistory who) = none
          rw [runtime.responseRecall_takeAction_position who budget execution action fragment
            position]
          have done : ¬ (fragment.actions ++ [action]).length < budget fragment.entry := by
            simp only [List.length_append, List.length_cons, List.length_nil] at length ⊢
            omega
          exact ite_eq_right done
      | cons next rest =>
          have unfinished : (fragment.actions ++ [action]).length < budget fragment.entry := by
            simp only [List.length_append, List.length_cons] at length ⊢
            simp only [List.length_nil] at *
            omega
          exact ih (runtime.takeAction who execution action)
            ⟨fragment.entry, fragment.actions ++ [action]⟩
            (runtime.responsePosition_takeAction who budget execution action fragment
              position unfinished) (List.cons_ne_nil _ _) (by
                simp only [List.length_append, List.length_cons, List.length_nil] at length ⊢
                omega)

/-- Completing exactly the inferred capacity returns the parser to a boundary.
The records may contain arbitrary actions, private data, and before-views. -/
theorem responseRecall_takeActions (runtime : EventGraphRuntime graph) (who : Player)
    (budget : NativeInput graph → Nat) (execution : NativeExecution runtime)
    (actions : List (PlayerAction graph))
    (boundary : responseRecall budget (execution.principalHistory who) = none)
    (length : actions.length = budget (runtime.nativeInput who execution)) :
    responseRecall budget
      ((runtime.takeActions who execution actions).principalHistory who) = none := by
  by_cases empty : actions = []
  · subst actions
    exact boundary
  · exact runtime.responseRecall_finish who budget execution actions
      ⟨runtime.nativeInput who execution, []⟩ (by
        change (responseRecall budget (execution.principalHistory who)).getD _ = _
        rw [boundary]
        rfl) empty (by simpa only [List.length_nil, Nat.zero_add] using length)

end Vegas.EventGraphRuntime
