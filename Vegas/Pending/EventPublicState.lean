/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication

/-! # Public tests for event readiness and commitment inclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace PublicView

/-- Readiness reconstructed from public completion identities alone. -/
def EventReady (view : PublicView graph) (event : graph.EventId) : Prop :=
  event ∉ view.observation.completionOrder ∧
    ∀ predecessor, predecessor ∈ graph.order.predecessors event →
      predecessor ∈ view.observation.completionOrder

instance (view : PublicView graph) (event : graph.EventId) :
    Decidable (view.EventReady event) := by
  unfold EventReady
  infer_instance

/-- Commitment acceptance depends only on public metadata, including for
unopenable handles. This test does not inspect a candidate's hidden meaning. -/
def BindingIncludable (runtime : EventGraphRuntime graph) (view : PublicView graph)
    (message : Message Player (Payload graph)) : Prop :=
  match message.payload with
  | .commitment event candidate =>
      view.EventReady event ∧
      (match view.activatedAt event with
        | none => False
        | some entered => view.clock - entered < runtime.deadline event) ∧
      (match nodeView graph event with
        | .bind owner _ _ _ => message.sender = owner ∧ candidate.1 = owner ∧
            view.accepted (.inr event) = none ∧ ∀ field, view.accepted field ≠ some candidate
        | _ => False)
  | _ => False

end PublicView

omit [DecidableEq Player] in
theorem State.publicView_eventReady (state : State graph) (event : graph.EventId) :
    state.publicView.EventReady event ↔ state.config.cut.Ready event := by
  constructor
  · rintro ⟨unfinished, predecessors⟩
    constructor
    · intro completed
      exact unfinished ((state.config.history_exact event).mpr completed)
    · intro predecessor member
      exact (state.config.history_exact predecessor).mp (predecessors predecessor member)
  · rintro ⟨unfinished, predecessors⟩
    constructor
    · intro inHistory
      exact unfinished ((state.config.history_exact event).mp inHistory)
    · intro predecessor member
      exact (state.config.history_exact predecessor).mpr (predecessors member)

theorem State.publicView_bindingIncludable (runtime : EventGraphRuntime graph)
    (state : State graph) (id : MessageId Player) (event : graph.EventId)
    (candidate : Handle graph) :
    state.publicView.BindingIncludable runtime ⟨id, .commitment event candidate⟩ ↔
      (handle runtime state ⟨id, .commitment event candidate⟩).isSome := by
  classical
  simp only [PublicView.BindingIncludable, state.publicView_eventReady]
  change (state.config.cut.Ready event ∧ state.WithinDeadline runtime event ∧ _) ↔ _
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView graph event <;>
        simp [handle, ready, timely, view, State.publicView, State.HandleUnused]
      split_ifs <;> simp_all
    · simp [handle, ready, timely]
  · simp [handle, ready]

end Vegas.EventGraphRuntime
