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

theorem acceptedRecorded_initial (inputs : graph.Inputs) :
    (initial inputs).AcceptedRecorded := rfl

theorem AcceptedRecorded.accepted_eq_of_order {left right : State graph}
    (leftRecorded : left.AcceptedRecorded) (rightRecorded : right.AcceptedRecorded)
    (order : (graph.publicObserve left.config).completionOrder =
      (graph.publicObserve right.config).completionOrder) : left.accepted = right.accepted := by
  rw [leftRecorded, rightRecorded, order,
    bindingRecords_inputs left.config.inputs right.config.inputs]

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

theorem AcceptedRecorded.complete_of_config {before after : State graph}
    (recorded : before.AcceptedRecorded) (event : graph.EventId)
    (ready : before.config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (nonbinding : ∀ owner payload, graph.outputLayout event ≠ .binding owner payload)
    (config : after.config = before.config.complete event ready action value)
    (accepted : after.accepted = before.accepted) : after.AcceptedRecorded := by
  exact (recorded.complete event ready action value nonbinding).transport accepted
    (congrArg (fun config => (graph.publicObserve config).completionOrder) config)

/-- Equal semantic observations reconstruct the dynamic private catalogue
without assuming any equality of accepted handles or initial catalogues. -/
theorem AcceptedRecorded.candidates_eq_of_observation {left right : State graph}
    (leftRecorded : left.AcceptedRecorded) (rightRecorded : right.AcceptedRecorded)
    (leftRepresented : left.CandidatesRepresented)
    (rightRepresented : right.CandidatesRepresented)
    (leftValid : left.BindingInvariant) (rightValid : right.BindingInvariant)
    (who : Player)
    (observed : graph.playerObserve who left.config = graph.playerObserve who right.config) :
    (fun slot => left.candidates.lookup (who, slot)) =
      fun slot => right.candidates.lookup (who, slot) := by
  have publicEq := publicObserve_eq_of_playerObserve_eq who left.config right.config observed
  exact leftRepresented.candidates_eq_of_observation rightRepresented leftValid rightValid who
    (leftRecorded.accepted_eq_of_order rightRecorded
      (congrArg PublicObservation.completionOrder publicEq)) observed

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

/-- Canonical binding packets establish the public accepted-handle decoder
through their actual protected inclusion, for usable and unusable values alike. -/
theorem reactiveBinding_reserved_recorded (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload))
    (recorded : execution.application.AcceptedRecorded)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (fresh : execution.application.candidates.lookup
      (owner, .prepared (execution.application.publicView.bindingCount owner)) = .fresh)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused
      (owner, .prepared (execution.application.publicView.bindingCount owner)))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (next : (runtime.reactiveApplication leaks).Execution)
    (supported : next ∈ (runtime.interactionStep leaks players network (.includeLatest event owner)
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload result
          (execution.application.publicView.bindingCount owner)))).support) :
    next.application.AcceptedRecorded := by
  obtain ⟨config, accepted, _candidates⟩ := runtime.reactiveBinding_reserved_state leaks execution
    owner event payload outputEq codeEq node result _ ready timely fresh vacant unused serials
      players network next supported
  exact recorded.binding event owner payload outputEq ready result config accepted

end Vegas.EventGraphRuntime
