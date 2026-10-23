/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCandidateRealization

/-! # Accepted handles reconstructed from public completion order

The canonical allocator assigns an owner's next prepared serial to its next
completed binding. The public event order therefore reconstructs every accepted
handle, independently of private binding values and deferred guard results.
The fold below encodes that public transcript; it does not execute the program.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private def allocationStep
    (record : (Player → Nat) × AcceptedHandles graph) (event : graph.EventId) :
    (Player → Nat) × AcceptedHandles graph :=
  match graph.outputLayout event with
  | .binding owner _ =>
      (Function.update record.1 owner (record.1 owner + 1),
        Function.update record.2 (.inr event) (some (owner, .prepared (record.1 owner))))
  | .publicData _ | .privateInput _ _ | .publication _ => record

/-- Public allocation counters and accepted handles after a completion list. -/
def bindingRecords (inputs : graph.Inputs) (order : List graph.EventId) :
    (Player → Nat) × AcceptedHandles graph :=
  order.foldl allocationStep (fun _ => 0, (State.initial inputs).accepted)

theorem bindingRecords_inputs (left right : graph.Inputs) (order : List graph.EventId) :
    bindingRecords left order = bindingRecords right order := rfl

theorem bindingRecords_append (inputs : graph.Inputs) (order : List graph.EventId)
    (event : graph.EventId) :
    bindingRecords inputs (order ++ [event]) =
      allocationStep (bindingRecords inputs order) event := by
  simp only [bindingRecords, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bindingRecords_count (inputs : graph.Inputs) (order : List graph.EventId) (who : Player) :
    (bindingRecords inputs order).1 who = order.countP (fun event =>
      match graph.outputLayout event with
      | .binding owner _ => decide (owner = who)
      | .publicData _ | .privateInput _ _ | .publication _ => false) := by
  induction order using List.reverseRecOn with
  | nil => rfl
  | append_singleton order event ih =>
      rw [bindingRecords_append]
      cases kind : graph.outputLayout event with
      | publicData payload | privateInput owner payload | publication payload =>
          simpa [allocationStep, kind] using ih
      | binding owner payload =>
          by_cases own : who = owner
          · subst who
            simp [allocationStep, kind, ih]
          · simp [allocationStep, kind, own, Ne.symm own, ih]

namespace State

/-- The real accepted table is encoded by its public completion order. -/
def AcceptedRecorded (state : State graph) : Prop :=
  state.accepted = (bindingRecords state.config.inputs
    (graph.publicObserve state.config).completionOrder).2

theorem AcceptedRecorded.transport {before after : State graph}
    (recorded : before.AcceptedRecorded) (accepted : after.accepted = before.accepted)
    (order : (graph.publicObserve after.config).completionOrder =
      (graph.publicObserve before.config).completionOrder) : after.AcceptedRecorded := by
  unfold AcceptedRecorded
  rw [accepted, order, bindingRecords_inputs after.config.inputs before.config.inputs]
  exact recorded

/-- Ordinary semantic completions retain accepted handles. Only the separate
canonical binding inclusion adds an association. -/
theorem AcceptedRecorded.complete {state : State graph} (recorded : state.AcceptedRecorded)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (nonbinding : ∀ owner payload, graph.outputLayout event ≠ .binding owner payload) :
    (state.complete event ready action value).AcceptedRecorded := by
  unfold AcceptedRecorded
  simp only [State.complete, publicObserve, Config.complete, List.map_append, List.map_singleton]
  rw [bindingRecords_append]
  cases kind : graph.outputLayout event with
  | publicData payload | privateInput owner payload | publication payload =>
      simpa only [allocationStep, kind, publicObserve] using
        (show state.accepted = _ from recorded)
  | binding owner payload => exact (nonbinding owner payload kind).elim

/-- The actual canonical association advances exactly the public allocation
record; its private result does not appear in this equation. -/
theorem AcceptedRecorded.binding {before after : State graph}
    (recorded : before.AcceptedRecorded) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (ready : before.config.cut.Ready event) (result : PublicationResult (L.Val payload))
    (config : after.config = before.config.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) result)
      (cast (congrArg EventField.Value outputEq.symm) result))
    (accepted : after.accepted = Function.update before.accepted (.inr event)
      (some (owner, .prepared (before.publicView.bindingCount owner)))) :
    after.AcceptedRecorded := by
  unfold AcceptedRecorded
  rw [config]
  simp only [publicObserve, Config.complete, List.map_append, List.map_singleton]
  rw [bindingRecords_append]
  simp only [allocationStep, outputEq]
  rw [accepted, recorded, bindingRecords_count]
  rfl

end State

end Vegas.EventGraphRuntime
