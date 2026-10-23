/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseRequestProgress
import Vegas.Pending.EventOpponentFrame
import Vegas.Pending.PhaseCurrentTokens
import Vegas.Pending.PhaseBindingService
import Vegas.Pending.PhaseOpeningAcceptance
import Interaction.ReactiveOwnerSelection
import Vegas.Pending.PhaseSeedScheduler
import Vegas.Pending.PhaseSeedOperationalInput
import Interaction.ReactiveRoundReachability
import Vegas.Pending.PhaseSeedServiceMarks

/-! # Other principals cannot resolve a ready private event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RecoveryState

private theorem inclusionResult_not_excluded_of_other (runtime : EventGraphRuntime graph)
    (state : RecoveryState graph) (native : State graph)
    (message : Message Player (Payload graph))
    (handled : EventGraphRuntime.handle runtime state.native message = some native)
    (owner : Player) (different : owner ≠ message.sender) (active : owner ∉ state.excluded) :
    owner ∉ (state.inclusionResult message.payload native).excluded := by
  obtain ⟨named, addressed, acting⟩ :=
    handle_event_actor runtime state.native native message handled
  cases call : message.payload with
  | commitment event candidate =>
      simpa only [inclusionResult, call] using active
  | malformed raw =>
      simp only [call, Payload.event?] at addressed
      cases addressed
  | opening event candidate raw =>
      rw [call] at addressed
      have same : named = event := (Option.some.inj addressed).symm
      subst named
      change owner ∉ (if publicationFailed native event then
        excludeEvent state.excluded event else state.excluded)
      split_ifs
      · rw [excludeEvent, acting]
        intro member
        rcases Finset.mem_insert.mp member with same | already
        · exact different same
        · exact active already
      · exact active

end RecoveryState

namespace PhaseRuntimeState

/-- An accepted packet of a different principal preserves the selected ready
request, even when normalization performs automatic service elsewhere. -/
theorem handle_foreign_request (runtime : EventGraphRuntime graph)
    {inputs : graph.Inputs} (state next : PhaseRuntimeState graph)
    (valid : state.Invariant inputs)
    (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : state.SeedRequest owner coordinate) (different : owner ≠ message.sender) :
    next.SeedRequest owner coordinate := by
  classical
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have progress := handle_progress runtime inputs state.current.native native
      ⟨message.id, message.payload.packet.call⟩ valid.active handled
    have unfinished : coordinate.event ∉ native.config.cut.completed := by
      intro completed
      exact requested.2.2.1.1 ((handle_opponent_completed_iff runtime state.current.native native
        ⟨message.id, message.payload.packet.call⟩ coordinate.event owner requested.2.2.2.1
          different handled).mp completed)
    have ready : native.config.cut.Ready coordinate.event :=
      (progress.ready_or_completed coordinate.event requested.2.2.1).resolve_left
        (fun completed => unfinished completed)
    have active := RecoveryState.inclusionResult_not_excluded_of_other runtime state.current
      native ⟨message.id, message.payload.packet.call⟩ handled owner different requested.2.2.2.2
    let raw : PhaseRuntimeState graph :=
      { state with current := state.current.inclusionResult message.payload.packet.call native }
    have beforeNormalize : raw.SeedRequest owner coordinate :=
      ⟨requested.1, requested.2.1, ready, requested.2.2.2.1, active⟩
    exact beforeNormalize.normalize.2
  · cases accepted

/-- Every packet accepted from the owner of a ready event names that very
semantic event. Same-owner ready uniqueness is supplied by the actual graph. -/
theorem handle_focal_event (runtime : EventGraphRuntime graph)
    (ordered : graph.RevealRelaxedOrdered) (state next : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : state.SeedRequest owner coordinate) (sender : message.sender = owner) :
    message.payload.packet.call.event? graph = some coordinate.event := by
  classical
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, handled, _⟩ := Option.map_eq_some_iff.mp accepted
    obtain ⟨event, named, ready, _action, _reached⟩ := handle_config_mem_step runtime
      state.current.native native ⟨message.id, message.payload.packet.call⟩ handled
    obtain ⟨actual, addressed, acting⟩ := handle_event_actor runtime state.current.native native
      ⟨message.id, message.payload.packet.call⟩ handled
    have sameNamed : actual = event := Option.some.inj (addressed.symm.trans named)
    subst actual
    have actingOwner : graph.actor? event = some owner := acting.trans (congrArg some sender)
    have same := ordered.ready_actor_unique state.current.native.config.cut requested.2.2.1
      ready requested.2.2.2.1 actingOwner
    exact named.trans (congrArg some same)
  · cases accepted

/-- A handled packet either leaves this owner's request intact, or is the
owner's own raw graph step at this coordinate. The raw witness is retained
across phase retirement and rollback rather than read from a later store. -/
theorem handle_request_or_own_completion (runtime : EventGraphRuntime graph)
    (ordered : graph.RevealRelaxedOrdered) {inputs : graph.Inputs}
    (state next : PhaseRuntimeState graph) (valid : state.Invariant inputs)
    (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : state.SeedRequest owner coordinate) :
    next.SeedRequest owner coordinate ∨
      ∃ (native : State graph) (ready : state.current.native.config.cut.Ready coordinate.event)
        (action : graph.Action coordinate.event),
        message.sender = owner ∧
        message.payload.packet.call.event? graph = some coordinate.event ∧
        EventGraphRuntime.handle runtime state.current.native
          ⟨message.id, message.payload.packet.call⟩ = some native ∧
        native.config ∈ (state.current.native.config.step coordinate.event ready action).support ∧
        next = ({state with current :=
          state.current.inclusionResult message.payload.packet.call native} :
            PhaseRuntimeState graph).normalize := by
  classical
  by_cases focal : message.sender = owner
  · have named := handle_focal_event runtime ordered state next message accepted owner coordinate
      requested focal
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, normalized⟩ := Option.map_eq_some_iff.mp accepted
      obtain ⟨event, addressed, ready, action, reached⟩ := handle_config_mem_step runtime
        state.current.native native ⟨message.id, message.payload.packet.call⟩ handled
      have same : event = coordinate.event := Option.some.inj (addressed.symm.trans named)
      subst event
      exact Or.inr ⟨native, ready, action, focal, named, handled, reached, normalized.symm⟩
    · cases accepted
  · exact Or.inl (handle_foreign_request runtime state next valid message accepted owner coordinate
      requested (Ne.symm focal))

end PhaseRuntimeState
end Vegas.EventGraphRuntime
