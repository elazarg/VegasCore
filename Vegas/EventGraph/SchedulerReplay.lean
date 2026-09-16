/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.NormalizedPolicy

/-! # Deterministic public-scheduler replay

This module replays only the public scheduling decisions of an event graph.
It does not execute nodes or sample their laws.  Public values are read from a
supplied later store and masked to the cut reached by the replay.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

variable (graph : Vegas.EventGraph Player L)

/-- A pure public scheduler.  Unlike `PublicScheduler`, it has no randomized
response left to sample. -/
def DeterministicPublicScheduler : Type :=
  (observation : graph.PublicObservation) →
  (enabled : Finset graph.EventId) → enabled.Nonempty →
    {event : graph.EventId // event ∈ enabled}

/-- Regard a deterministic scheduler as a degenerate randomized scheduler. -/
def DeterministicPublicScheduler.toPublic
    (scheduler : graph.DeterministicPublicScheduler) : graph.PublicScheduler :=
  fun observation enabled nonempty => FinDist.pure (scheduler observation enabled nonempty)

/-- Retain exactly the public fields available at a replayed cut.  The input
store may come from a later player observation; private bindings and public
outputs not yet replayed are absent from the scheduler observation. -/
def replayPublicStore (cut : graph.order.Cut)
    (store : EventGraph.Store graph.layout) : EventGraph.Store graph.layout :=
  fun field =>
    if graph.FieldAvailable cut field then graph.publicStore store field else none

/-- Replay at most `fuel` pure scheduler selections.  The target event is not
completed: success returns the chronological prefix immediately before the
scheduler selects it. -/
def replayPrefixAux (scheduler : graph.DeterministicPublicScheduler)
    (target : graph.EventId) (store : EventGraph.Store graph.layout) :
    Nat → graph.order.Cut → List graph.EventId → Option (List graph.EventId)
  | 0, _, _ => none
  | fuel + 1, cut, order =>
      if terminal : cut.Terminal then none
      else
        let enabledNonempty : cut.enabled.Nonempty := by
          obtain ⟨event, ready⟩ := cut.exists_ready_of_not_terminal terminal
          exact ⟨event, (EventOrder.Cut.mem_enabled _ _).mpr ready⟩
        let selected := scheduler
          { completionOrder := order
            store := graph.replayPublicStore cut store }
          cut.enabled enabledNonempty
        if same : selected.1 = target then
          some order
        else
          have ready : cut.Ready selected.1 :=
            (EventOrder.Cut.mem_enabled _ _).mp selected.2
          replayPrefixAux scheduler target store fuel
            (cut.complete selected.1 ready) (order ++ [selected.1])

omit [DecidableEq Player] in
/-- A total scheduler must select every still-unfinished target before it can
exhaust a fuel bound larger than the number of unfinished events. -/
theorem replayPrefixAux_isSome (scheduler : graph.DeterministicPublicScheduler)
    (target : graph.EventId) (store : EventGraph.Store graph.layout)
    (fuel : Nat) (cut : graph.order.Cut) (order : List graph.EventId)
    (unfinished : target ∉ cut.completed)
    (enough : graph.order.eventCount - cut.completed.card < fuel) :
    (graph.replayPrefixAux scheduler target store fuel cut order).isSome = true := by
  induction fuel generalizing cut order with
  | zero => omega
  | succ fuel ih =>
      unfold replayPrefixAux
      split <;> rename_i terminal
      · unfold EventOrder.Cut.Terminal at terminal
        rw [terminal] at unfinished
        simp at unfinished
      · dsimp only
        split <;> rename_i same
        · simp
        · apply ih
          · simp only [EventOrder.Cut.completed_complete, Finset.mem_insert]
            exact fun membership => unfinished
              (membership.resolve_left (fun equal => same equal.symm))
          · rw [EventOrder.Cut.card_complete]
            have cardLt : cut.completed.card < graph.order.eventCount := by
              have targetMem : target ∈ (Finset.univ : Finset graph.EventId) :=
                Finset.mem_univ target
              simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
                ⟨Finset.subset_univ cut.completed, fun equal => unfinished (equal ▸ targetMem)⟩)
            omega

/-- Replay from the empty cut for the maximum possible number of scheduler
selections before a target is chosen. -/
def replayPrefix? (scheduler : graph.DeterministicPublicScheduler)
    (target : graph.EventId) (store : EventGraph.Store graph.layout) :
    Option (List graph.EventId) :=
  graph.replayPrefixAux scheduler target store (graph.order.eventCount + 1)
    (EventOrder.Cut.empty graph.order) []

omit [DecidableEq Player] in
@[simp] theorem replayPrefix?_isSome
    (scheduler : graph.DeterministicPublicScheduler) (target : graph.EventId)
    (store : EventGraph.Store graph.layout) :
    (graph.replayPrefix? scheduler target store).isSome = true := by
  apply graph.replayPrefixAux_isSome scheduler target store
  · simp [EventOrder.Cut.empty]
  · simp [EventOrder.Cut.empty]

/-- The scheduler's total replay prefix. -/
def replayPrefix (scheduler : graph.DeterministicPublicScheduler)
    (target : graph.EventId) (store : EventGraph.Store graph.layout) :
    List graph.EventId :=
  (graph.replayPrefix? scheduler target store).get
    (by simp)

/-- Reinterpret an arbitrary order-sensitive policy canonically by rebuilding
the pure scheduler's order from the retained store. -/
def replayPolicy (scheduler : graph.DeterministicPublicScheduler) (who : Player)
    (policy : graph.BehavioralPolicy who) : graph.BehavioralPolicy who :=
  fun event actor observation =>
    policy event actor
      { observation with
        completionOrder := graph.replayPrefix scheduler event observation.store }

omit [DecidableEq Player] in
@[simp] theorem replayPolicy_apply
    (scheduler : graph.DeterministicPublicScheduler) (who : Player)
    (policy : graph.BehavioralPolicy who) (event : graph.EventId)
    (actor : graph.actor? event = some who) (observation : graph.PlayerObservation who) :
    graph.replayPolicy scheduler who policy event actor observation =
      policy event actor
        { observation with
          completionOrder := graph.replayPrefix scheduler event observation.store } := rfl

omit [DecidableEq Player] in
/-- Replaying a scheduler is insensitive to the completion-order component of
the supplied player observation. -/
theorem replayPolicy_observation_congr
    (scheduler : graph.DeterministicPublicScheduler) (who : Player)
    (policy : graph.BehavioralPolicy who) (event : graph.EventId)
    (actor : graph.actor? event = some who)
    (left right : graph.PlayerObservation who)
    (store : left.store = right.store) (actions : left.ownActions = right.ownActions) :
    graph.replayPolicy scheduler who policy event actor left =
      graph.replayPolicy scheduler who policy event actor right := by
  apply congrArg (policy event actor)
  apply PlayerObservation.ext graph
  · simp [store]
  · exact store
  · exact actions

omit [DecidableEq Player] in
/-- Replay policies are fixed points of completion-order normalization. -/
theorem normalizePolicy_replayPolicy
    (scheduler : graph.DeterministicPublicScheduler) (who : Player)
    (policy : graph.BehavioralPolicy who) :
    graph.normalizePolicy who (graph.replayPolicy scheduler who policy) =
      graph.replayPolicy scheduler who policy := by
  funext event actor observation
  apply graph.replayPolicy_observation_congr scheduler who policy event actor
  · rfl
  · rfl

end Vegas.EventGraph
