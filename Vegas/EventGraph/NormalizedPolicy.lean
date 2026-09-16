/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.BarrierInformation
import Vegas.EventGraph.Semantics

/-! # Source-rank-normalized event-graph policies

Canonical policies retain the actor's visible store and original own actions,
but receive a completion order determined only by the current event's fixed
topological rank.  This removes asynchronous scheduling metadata without
changing the executable graph or reconstructing actions from outputs.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

variable (graph : Vegas.EventGraph Player L)

/-- All event identities strictly before one event in the graph's fixed rank. -/
def rankPrefix (event : graph.EventId) : List graph.EventId :=
  (List.finRange graph.order.eventCount).filter fun prior => prior.val < event.val

omit [DecidableEq Player] in
@[simp] theorem mem_rankPrefix (event prior : graph.EventId) :
    prior ∈ graph.rankPrefix event ↔ prior.val < event.val := by
  simp [rankPrefix]

/-- Replace chronological scheduling metadata by the fixed source-rank prefix,
while retaining the actor's entire projected store and original own actions. -/
def normalizeObservation (event : graph.EventId) (who : Player)
    (observation : graph.PlayerObservation who) : graph.PlayerObservation who where
  completionOrder := graph.rankPrefix event
  store := observation.store
  ownActions := observation.ownActions

omit [DecidableEq Player] in
@[simp] theorem normalizeObservation_store (event : graph.EventId) (who : Player)
    (observation : graph.PlayerObservation who) :
    (graph.normalizeObservation event who observation).store = observation.store := rfl

omit [DecidableEq Player] in
@[simp] theorem normalizeObservation_ownActions (event : graph.EventId) (who : Player)
    (observation : graph.PlayerObservation who) :
    (graph.normalizeObservation event who observation).ownActions = observation.ownActions := rfl

omit [DecidableEq Player] in
@[simp] theorem normalizeObservation_completionOrder (event : graph.EventId)
    (who : Player) (observation : graph.PlayerObservation who) :
    (graph.normalizeObservation event who observation).completionOrder =
      graph.rankPrefix event := rfl

/-- Compile a canonical behavioral policy to ignore actual completion order. -/
def normalizePolicy (who : Player) (policy : graph.BehavioralPolicy who) :
    graph.BehavioralPolicy who :=
  fun event actor observation =>
    policy event actor (graph.normalizeObservation event who observation)

/-- Normalize every player policy independently. -/
def normalizeProfile (profile : graph.BehavioralProfile) : graph.BehavioralProfile :=
  fun who => graph.normalizePolicy who (profile who)

omit [DecidableEq Player] in
@[simp] theorem normalizePolicy_idempotent (who : Player)
    (policy : graph.BehavioralPolicy who) :
    graph.normalizePolicy who (graph.normalizePolicy who policy) =
      graph.normalizePolicy who policy := rfl

omit [DecidableEq Player] in
@[simp] theorem normalizeProfile_idempotent (profile : graph.BehavioralProfile) :
    graph.normalizeProfile (graph.normalizeProfile profile) =
      graph.normalizeProfile profile := rfl

/-- Normalization acts independently on each player's policy. -/
@[simp] theorem normalizeProfile_update (profile : graph.BehavioralProfile)
    (who : Player) (replacement : graph.BehavioralPolicy who) :
    graph.normalizeProfile
        (GameTheory.Profile.update (sig := graph.gameSignature) profile who replacement) =
      GameTheory.Profile.update (sig := graph.gameSignature)
        (graph.normalizeProfile profile) who (graph.normalizePolicy who replacement) := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [normalizeProfile, GameTheory.Profile.update_same]
  · simp only [normalizeProfile, GameTheory.Profile.update_of_ne _ _ same]

omit [DecidableEq Player] in
private theorem actor_output_visible {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (who : Player) (actor : code.actor = some who) :
    output.VisibleTo who := by
  cases code <;> simp_all [EventCode.actor, EventField.VisibleTo]

/-- At a ready strategic event, normalization changes only completion-order
metadata.  The barrier information certificate says the retained store and
own actions are exactly the canonical logical observation. -/
theorem BarrierOrdered.normalizeObservation_eq_logical
    {graph : Vegas.EventGraph Player L} (ordered : graph.BarrierOrdered)
    (config : graph.Config) (event : graph.EventId) (who : Player)
    (ready : config.cut.Ready event) (actor : graph.actor? event = some who) :
    graph.normalizeObservation event who (graph.playerObserve who config) =
      { completionOrder := graph.rankPrefix event
        store := (graph.logicalObserve graph.prefixSchema event who
          (graph.playerObserve who config)).store
        ownActions := (graph.logicalObserve graph.prefixSchema event who
          (graph.playerObserve who config)).ownActions } := by
  apply PlayerObservation.ext graph
  · rfl
  · exact (ordered.informationDiscipline.logicalObserve_store
      config event who ready actor).symm
  · exact (ordered.informationDiscipline.logicalObserve_ownActions
      config event who ready actor).symm

/-- Two simultaneously ready strategic events with different owners cannot
expose one event's output to the other actor under public-barrier ordering.
Any public event would force one of the two events to wait. -/
theorem BarrierOrdered.simultaneous_foreign_hidden
    {graph : Vegas.EventGraph Player L} (ordered : graph.BarrierOrdered)
    {cut : graph.order.Cut} {event other : graph.EventId} {who foreign : Player}
    (eventReady : cut.Ready event) (otherReady : cut.Ready other)
    (actor : graph.actor? event = some who)
    (otherActor : graph.actor? other = some foreign) (differentOwner : foreign ≠ who) :
    ¬ graph.fieldVisibleTo who (.inr other) := by
  have different : event ≠ other := by
    intro same
    subst other
    have owners : who = foreign := Option.some.inj (actor.symm.trans otherActor)
    exact differentOwner owners.symm
  have notPublic : ¬ (graph.outputLayout other).IsPublic := by
    intro isPublic
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne different) with before | after
    · have predecessor : event ∈ graph.order.predecessors other := by
        rw [ordered other]
        exact barrierOrder_public_event graph.outputLayout before isPublic
      exact eventReady.1 (otherReady.2 predecessor)
    · have predecessor : other ∈ graph.order.predecessors event := by
        rw [ordered event]
        exact barrierOrder_public_prior graph.outputLayout after isPublic
      exact otherReady.1 (eventReady.2 predecessor)
  have visibleForeign : (graph.outputLayout other).VisibleTo foreign :=
    actor_output_visible (graph.nodes other) foreign otherActor
  intro visibleWho
  change (graph.outputLayout other).VisibleTo who at visibleWho
  cases kind : graph.outputLayout other <;>
    simp_all [EventField.IsPublic, EventField.VisibleTo]

/-- Completing a simultaneously-ready foreign strategic event leaves the
normalized prescribed kernel at the retained event exactly unchanged.  The
foreign event is necessarily hidden by the public-barrier discipline; its
completion also leaves the retained event ready. -/
theorem BarrierOrdered.normalizePolicy_complete_foreign
    {graph : Vegas.EventGraph Player L} {who : Player}
    (ordered : graph.BarrierOrdered)
    (policy : graph.BehavioralPolicy who) (config : graph.Config)
    (event other : graph.EventId) (eventReady : config.cut.Ready event)
    (otherReady : config.cut.Ready other) (actor : graph.actor? event = some who)
    (foreign : Player) (otherActor : graph.actor? other = some foreign)
    (differentOwner : foreign ≠ who) (action : graph.Action other)
    (value : (graph.outputLayout other).Value) :
    let next := config.complete other otherReady action value
    next.cut.Ready event ∧
      graph.normalizePolicy who policy event actor
          (graph.playerObserve who next) =
        graph.normalizePolicy who policy event actor
          (graph.playerObserve who config) := by
  have different : event ≠ other := by
    intro same
    subst other
    have owners : who = foreign := Option.some.inj (actor.symm.trans otherActor)
    exact differentOwner owners.symm
  have retainedReady := eventReady.after_complete otherReady different
  have hidden := ordered.simultaneous_foreign_hidden eventReady otherReady actor
    otherActor differentOwner
  have storeEq := graph.playerStore_complete_of_hidden who config other otherReady
    action value hidden
  have notOwned : graph.actor? other ≠ some who := by
    rw [otherActor]
    simpa using differentOwner
  have actionsEq := graph.ownCompletions_complete_of_not_actor who config other
    otherReady action value notOwned
  refine ⟨retainedReady, ?_⟩
  apply congrArg (policy event actor)
  apply PlayerObservation.ext graph
  · rfl
  · exact storeEq
  · exact actionsEq

end Vegas.EventGraph
