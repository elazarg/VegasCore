/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowDrain

/-! # Successful binding preservation along actual automatic recovery

The refinement premise is an independent invariant of a bad-only repair.
It is not a property of arbitrary private shadows. The whole drain proof
uses the existing automatic-step path, without constructing another runner.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- A failure completion cannot change a successful binding to a different
value on either side. This includes deferred publication failure. -/
theorem completeFailure_bindingRefines (left right : State graph)
    (event : graph.EventId) (leftReady : left.config.cut.Ready event)
    (rightReady : right.config.cut.Ready event)
    (preserved : left.config.store.BindingRefines right.config.store) :
    (left.completeFailure event leftReady).config.store.BindingRefines
      (right.completeFailure event rightReady).config.store := by
  cases node : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      simp only [State.completeFailure, node]
      apply Config.bindingRefines_complete preserved event leftReady rightReady
      apply EventField.BindingRefines.cast_some outputEq.symm
      exact EventField.BindingRefines.refl _ _
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [State.completeFailure, node]
      apply Config.bindingRefines_complete preserved event leftReady rightReady
      apply EventField.BindingRefines.cast_some outputEq.symm
      trivial
  | sample payload law outputEq codeEq =>
      simpa only [State.completeFailure, node] using preserved

/-- One actual automatic transition retains both the supported logical
shadow and the separately supplied successful-store refinement. -/
theorem CompletedAt.automatic_refinement {memory : BindingShadow graph}
    {state : RecoveryState graph} (supported : memory.CompletedAt state.native.config)
    (owner : Player)
    (preserved : (memory.native owner state.native).config.store.BindingRefines
      state.native.config.store)
    (event : graph.EventId) (eligible : state.AutomaticReady event) :
    memory.CompletedAt (state.completeAutomatic event eligible).native.config ∧
      Store.BindingRefines
        (memory.native owner (state.completeAutomatic event eligible).native).config.store
        (state.completeAutomatic event eligible).native.config.store := by
  have sameMask := restrictCompleted_eq_of_completedAt memory state.native.config supported
  have commutes := restrictCompleted_completeAutomatic memory owner
    state.native.config.cut.completed state event eligible (fun _ member => member)
  rw [sameMask] at commutes
  have moved := completeFailure_bindingRefines (memory.native owner state.native)
    state.native event eligible.1 eligible.1 preserved
  have nextSupported :
      memory.CompletedAt (state.completeAutomatic event eligible).native.config := by
    intro prior present
    obtain ⟨action, realized⟩ := state.completeAutomatic_step event eligible
    rw [state.native.config.step_cut event eligible.1 action _ realized]
    exact state.native.config.cut.completed_subset_complete event eligible.1
      (supported prior present)
  refine ⟨nextSupported, ?_⟩
  have native := congrArg RecoveryState.native commutes
  change memory.native owner (state.completeAutomatic event eligible).native =
    (memory.native owner state.native).completeFailure event eligible.1 at native
  rw [native]
  exact moved

/-- The exact existing automatic path transports refinement through every
excluded-owner completion, including rebuilt retry checkpoints. -/
theorem CompletedAt.phase_drain_refinement {memory : BindingShadow graph}
    {state : RecoveryState graph} (supported : memory.CompletedAt state.native.config)
    (owner : Player)
    (preserved : (memory.native owner state.native).config.store.BindingRefines
      state.native.config.store) (phase : RuntimePhase graph) :
    (memory.native owner (phase.drain state).native).config.store.BindingRefines
      (phase.drain state).native.config.store := by
  have along (last : RecoveryState graph)
      (path : Relation.ReflTransGen (RuntimePhase.AutomaticStep phase) state last) :
      memory.CompletedAt last.native.config ∧
        (memory.native owner last.native).config.store.BindingRefines last.native.config.store := by
    induction path with
    | refl => exact ⟨supported, preserved⟩
    | tail _ step ih =>
        obtain ⟨event, eligible, rfl⟩ := step
        exact ih.1.automatic_refinement owner ih.2 event eligible.2
  exact (along _ (phase.drain_trace state)).2

end Vegas.EventGraphRuntime.BindingShadow
