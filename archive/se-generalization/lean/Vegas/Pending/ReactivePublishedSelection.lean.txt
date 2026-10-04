/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveService

/-! # Reserved inclusion ignores already published envelopes

The event-addressed selector depends only on the ordered list of unpublished
pending envelopes and the public ledger.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Removing published identifiers leaves the actual reserved command unchanged. -/
theorem reactiveLatest_filter_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) :
    runtime.reactiveLatest leaks event owner
        { view with network.pending := view.network.pending.filter fun message =>
          message.id ∉ view.network.ledger.map Message.id } =
      runtime.reactiveLatest leaks event owner view := by
  unfold reactiveLatest
  simp only [ReactiveApplication.EnvironmentView.Unpublished, ← List.filter_reverse,
    List.find?_filter]
  congr 1
  congr 1
  funext message
  simp [and_comm, and_left_comm]

/-- Arbitrary inserted or removed spent copies are irrelevant when the remaining
pending order and ledger agree. No application-state equality is needed. -/
theorem reactiveLatest_eq_of_unpublished_pending_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player)
    (left right : (runtime.reactiveApplication leaks).EnvironmentView)
    (ledger : left.network.ledger = right.network.ledger)
    (pending : left.network.pending.filter (fun message =>
        message.id ∉ left.network.ledger.map Message.id) =
      right.network.pending.filter (fun message =>
        message.id ∉ right.network.ledger.map Message.id)) :
    runtime.reactiveLatest leaks event owner left =
      runtime.reactiveLatest leaks event owner right := by
  rw [← runtime.reactiveLatest_filter_published leaks event owner left,
    ← runtime.reactiveLatest_filter_published leaks event owner right]
  unfold reactiveLatest
  simp only [ReactiveApplication.EnvironmentView.Unpublished]
  rw [pending]
  simp only [ledger]

end Vegas.EventGraphRuntime
