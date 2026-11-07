/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionCompletion

/-! # Outputs of automatic completion

Automatic completion completes a defaulted owner's ready event with its forced
failure. So every event a drain completes stores the failure of its kind: a
failed binding or a failed publication.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The failure an event's forced completion stores: a failed binding or a
failed publication; none for chance. -/
def failureOutput (event : graph.EventId) : Option (graph.outputLayout event).Value :=
  match nodeView graph event with
  | .bind _ _ outputEq _ => some (cast (congrArg EventField.Value outputEq.symm) .failure)
  | .resolve _ _ _ _ outputEq _ => some (cast (congrArg EventField.Value outputEq.symm) .failure)
  | .sample .. => none

namespace State

/-- A forced failure of an owned event stores its failure. -/
theorem completeFailure_outputs_self (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player)
    (owned : graph.actor? event = some owner) :
    (state.completeFailure event ready).config.outputs event = failureOutput event := by
  unfold completeFailure failureOutput
  cases view : nodeView graph event with
  | bind => simp [complete, Config.complete]
  | resolve => simp [complete, Config.complete]
  | sample payload law outputEq codeEq =>
      exfalso
      have ownerless := nodeView_sample_actor outputEq codeEq
      rw [ownerless] at owned
      cases owned

/-- A forced failure keeps every other output. -/
theorem completeFailure_outputs_of_ne (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) {other : graph.EventId} (different : other ≠ event) :
    (state.completeFailure event ready).config.outputs other = state.config.outputs other := by
  unfold completeFailure
  cases nodeView graph event with
  | bind => exact state.config.complete_output_of_ne event other ready _ _ different
  | resolve => exact state.config.complete_output_of_ne event other ready _ _ different
  | sample => rfl

/-- **Drained events store their failure.** -/
theorem drain_outputs (state : State graph) (event : graph.EventId)
    (fresh : event ∉ state.config.cut.completed)
    (drained : event ∈ state.drain.config.cut.completed) :
    state.drain.config.outputs event = failureOutput event := by
  have invariant := drainFuel_induction (fun current : State graph => ∀ other,
      other ∉ state.config.cut.completed → other ∈ current.config.cut.completed →
        current.config.outputs other = failureOutput other)
    (fun before chosen eligible previous other otherFresh otherDone => by
      obtain ⟨owner, owned, _⟩ := eligible.owned
      by_cases same : other = chosen
      · subst same
        exact completeFailure_outputs_self before other eligible.1 owner owned
      · have earlier : other ∈ before.config.cut.completed := by
          obtain ⟨action, member⟩ := before.completeAutomatic_step chosen eligible
          rw [before.config.step_cut chosen eligible.1 action _ member,
            EventOrder.Cut.mem_complete] at otherDone
          exact otherDone.resolve_left same
        change (before.completeFailure chosen eligible.1).config.outputs other = _
        rw [completeFailure_outputs_of_ne before chosen eligible.1 same]
        exact previous other otherFresh earlier)
    state.config.remaining state (fun other otherFresh otherDone => (otherFresh otherDone).elim)
  exact invariant event fresh drained

end State

end Vegas.EventGraphRuntime
