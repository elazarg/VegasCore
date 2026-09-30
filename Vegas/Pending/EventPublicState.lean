/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication
import Vegas.EventGraph.BarrierInformation

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

/-- `event` is `who`'s turn: it is ready, `who` acts there, and `who` acts at
no other ready event. Under the barrier order every ready strategic event is
its actor's turn (`State.ownTurn_of_ready`). -/
def OwnTurn (view : PublicView graph) (who : Player) (event : graph.EventId) : Prop :=
  view.EventReady event ∧ graph.actor? event = some who ∧
    ∀ other, view.EventReady other → graph.actor? other = some who → other = event

open Classical in
/-- The least ready event at which `who` acts, if any. Prescribed clients
serve this event; no service grant is consulted. -/
def ownTurn? (view : PublicView graph) (who : Player) : Option graph.EventId :=
  (List.finRange graph.order.eventCount).find? fun event =>
    decide (view.EventReady event ∧ graph.actor? event = some who)

theorem ownTurn?_spec (view : PublicView graph) (who : Player) (event : graph.EventId)
    (selected : view.ownTurn? who = some event) :
    view.EventReady event ∧ graph.actor? event = some who := by
  classical
  unfold ownTurn? at selected
  have chosen := List.find?_some selected
  exact of_decide_eq_true chosen

theorem ownTurn?_of_ownTurn (view : PublicView graph) (who : Player) (event : graph.EventId)
    (turn : view.OwnTurn who event) : view.ownTurn? who = some event := by
  classical
  cases selected : view.ownTurn? who with
  | none =>
      unfold ownTurn? at selected
      have missing := List.find?_eq_none.mp selected event (List.mem_finRange event)
      exact absurd (decide_eq_true ⟨turn.1, turn.2.1⟩) missing
  | some chosen =>
      obtain ⟨ready, actor⟩ := view.ownTurn?_spec who chosen selected
      rw [turn.2.2 chosen ready actor]

/-- `who` acts at no ready event: it is nobody's turn to serve for `who`. -/
def Idle (view : PublicView graph) (who : Player) : Prop :=
  ∀ event, view.EventReady event → graph.actor? event ≠ some who

theorem ownTurn?_eq_none (view : PublicView graph) (who : Player) (idle : view.Idle who) :
    view.ownTurn? who = none := by
  classical
  unfold ownTurn?
  apply List.find?_eq_none.mpr
  intro event _ selected
  exact idle event (of_decide_eq_true selected).1 (of_decide_eq_true selected).2

/-- `event` is the only ready event. In a sequentialized graph every ready event
is; under the barrier order a ready public event is. Other players then have
no turn while it is served. -/
def SoleReady (view : PublicView graph) (event : graph.EventId) : Prop :=
  view.EventReady event ∧ ∀ other, view.EventReady other → other = event

omit [DecidableEq Player] in
theorem SoleReady.ownTurn {view : PublicView graph} {event : graph.EventId}
    (sole : view.SoleReady event) {who : Player} (owned : graph.actor? event = some who) :
    view.OwnTurn who event :=
  ⟨sole.1, owned, fun other ready _ => sole.2 other ready⟩

omit [DecidableEq Player] in
theorem SoleReady.idle {view : PublicView graph} {event : graph.EventId}
    (sole : view.SoleReady event) {who : Player} (foreign : graph.actor? event ≠ some who) :
    view.Idle who :=
  fun other ready actor => foreign (sole.2 other ready ▸ actor)

theorem SoleReady.ownTurn?_foreign {view : PublicView graph} {event : graph.EventId}
    (sole : view.SoleReady event) {who : Player} (foreign : graph.actor? event ≠ some who) :
    view.ownTurn? who = none :=
  view.ownTurn?_eq_none who (sole.idle foreign)

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

/-- Under the barrier order every ready event is its actor's turn. -/
theorem State.ownTurn_of_ready (state : State graph) (ordered : graph.BarrierOrdered)
    (who : Player) (event : graph.EventId) (ready : state.publicView.EventReady event)
    (actor : graph.actor? event = some who) : state.publicView.OwnTurn who event :=
  ⟨ready, actor, fun other otherReady otherActor =>
    ordered.ready_actor_unique state.config.cut ((state.publicView_eventReady event).mp ready)
      ((state.publicView_eventReady other).mp otherReady) actor otherActor⟩

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

/-- A withholding packet is accepted exactly at a timely, ready revelation
owned by its author. Hidden binding values and remembered intentions do not
enter this test. -/
theorem handle_withhold_isSome_iff (runtime : EventGraphRuntime graph)
    (state : State graph) (id : MessageId Player) (event : graph.EventId) :
    (handle runtime state ⟨id, .withhold event⟩).isSome = true ↔
      state.config.cut.Ready event ∧ state.WithinDeadline runtime event ∧
        match nodeView graph event with
        | .resolve owner _ _ _ _ _ => id.1 = owner
        | _ => False := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases node : nodeView graph event with
      | bind | sample => simp [handle, ready, timely, node]
      | resolve owner payload binding checks outputEq codeEq =>
          by_cases sender : id.1 = owner
          · simp only [handle, ready, timely, node, Message.sender, sender, ↓reduceDIte,
              and_self]
            change ((EventCode.resolveOutput? binding checks _
              state.config.store).bind _).isSome = true ↔ True
            simp only [Option.isSome_bind]
            change (EventCode.resolveOutput? binding checks _ state.config.store).isSome = true ↔
              True
            have defined (disclose : Bool) :
                (EventCode.resolveOutput? binding checks disclose state.config.store).isSome =
                  true := by
              apply EventCode.resolveOutput?_isSome
              intro field read
              apply state.config.read_available ready
              rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
              exact read
            simp only [defined, iff_self]
          · simp [handle, ready, timely, node, Message.sender, sender]
    · simp [handle, ready, timely]
  · simp [handle, ready]

end Vegas.EventGraphRuntime
