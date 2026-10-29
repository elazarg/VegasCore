/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventApplication
import Vegas.EventGraph.RevealRelaxation

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
  message.sender ∉ view.observation.defaulted ∧ match message.payload with
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
serve this event. -/
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

/-- Under reveal-relaxed ordering every ready event is its actor's turn. -/
theorem State.ownTurn_of_ready (state : State graph) (ordered : graph.RevealRelaxedOrdered)
    (who : Player) (event : graph.EventId) (ready : state.publicView.EventReady event)
    (actor : graph.actor? event = some who) : state.publicView.OwnTurn who event :=
  ⟨ready, actor, fun other otherReady otherActor =>
    ordered.ready_actor_unique state.config.cut ((state.publicView_eventReady event).mp ready)
      ((state.publicView_eventReady other).mp otherReady) actor otherActor⟩

omit [DecidableEq Player] in
/-- A sender whose contract state has the event ready attaches its token. -/
theorem State.publicView_tokenFor_of_ready (state : State graph) (packet : Payload graph)
    (event : graph.EventId) (named : packet.event? graph = some event)
    (ready : state.config.cut.Ready event) :
    state.publicView.tokenFor packet = some ⟨event⟩ :=
  state.publicView.tokenFor_eq_some packet event named
    ((state.publicView_eventReady event).mpr ready).2

omit [DecidableEq Player] in
/-- A publicly ready event has its token issued. -/
theorem PublicView.tokenFor_of_eventReady (view : PublicView graph) (packet : Payload graph)
    (event : graph.EventId) (named : packet.event? graph = some event)
    (ready : view.EventReady event) :
    view.tokenFor packet = some ⟨event⟩ :=
  view.tokenFor_eq_some packet event named ready.2

theorem State.publicView_bindingIncludable (runtime : EventGraphRuntime graph)
    (state : State graph) (id : MessageId Player) (event : graph.EventId)
    (candidate : Handle graph) :
    state.publicView.BindingIncludable runtime ⟨id, .commitment event candidate⟩ ↔
      (handle runtime state ⟨id, .commitment event candidate⟩).isSome := by
  classical
  simp only [PublicView.BindingIncludable, state.publicView_eventReady]
  change (id.1 ∉ state.config.defaulted ∧ state.config.cut.Ready event ∧
    state.WithinDeadline runtime event ∧ _) ↔ _
  by_cases inactive : id.1 ∈ state.config.defaulted
  · simp [inactive, handle, Message.sender]
  simp only [inactive, not_false_eq_true, true_and]
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView graph event <;>
        simp [handle, Message.sender, inactive, ready, timely, view,
          State.publicView, State.HandleUnused]
      split_ifs <;> simp_all
    · simp [handle, Message.sender, inactive, ready, timely]
  · simp [handle, Message.sender, inactive, ready]

/-- The number of completed binding instructions owned by this player. -/
def PublicView.bindingCount (view : PublicView graph) (who : Player) : Nat :=
  view.observation.completionOrder.countP fun event =>
    match graph.outputLayout event with
    | .binding owner _ => decide (owner = who)
    | .publicData _ | .privateInput _ _ | .publication _ => false

end Vegas.EventGraphRuntime
