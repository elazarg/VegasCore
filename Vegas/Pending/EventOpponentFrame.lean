/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventHonestBoundary

/-! # Native frames for opponent-owned events

Pointwise frame facts used when a focal player takes native private or
submission actions while another player's event remains under analysis.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Acceptance authenticates the packet sender as the actor of the uniquely
addressed event. Thus player-authored traffic can complete only that player's
events; chance events are completed only by environment commands. -/
theorem handle_event_actor
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    ∃ event, Payload.event? graph message.payload = some event ∧
      graph.actor? event = some message.sender := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | resolve | sample => simp [handle, ready, timely, view] at accepted
          | bind owner payload outputEq codeEq =>
              simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
              split at accepted
              · rename_i sender
                have codeActor := congrArg EventCode.actor codeEq
                rw [EventCode.actor_cast outputEq (graph.nodes event)] at codeActor
                refine ⟨event, rfl, ?_⟩
                simpa only [EventGraph.actor?, EventCode.actor, Message.sender] using
                  codeActor.trans (congrArg some sender.symm)
              · simp_all
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | opening event candidate raw =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | bind | sample => simp [handle, ready, timely, view] at accepted
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
              split at accepted
              · rename_i sender
                have codeActor := congrArg EventCode.actor codeEq
                rw [EventCode.actor_cast outputEq (graph.nodes event)] at codeActor
                refine ⟨event, rfl, ?_⟩
                simpa only [EventGraph.actor?, EventCode.actor, Message.sender] using
                  codeActor.trans (congrArg some sender.symm)
              · simp_all
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | withhold event =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | bind | sample => simp [handle, ready, timely, view] at accepted
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
              split at accepted
              · rename_i sender
                have codeActor := congrArg EventCode.actor codeEq
                rw [EventCode.actor_cast outputEq (graph.nodes event)] at codeActor
                refine ⟨event, rfl, ?_⟩
                simpa only [EventGraph.actor?, EventCode.actor, Message.sender] using
                  codeActor.trans (congrArg some sender.symm)
              · simp_all
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted

/-- Applying an accepted focal-authored packet cannot consume an event owned
by another player.  This is the completion-set form used by boundary frames. -/
theorem handle_opponent_completed_iff
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph))
    (event : graph.EventId) (owner : Player)
    (actor : graph.actor? event = some owner) (different : owner ≠ message.sender)
    (accepted : handle runtime state message = some next) :
    event ∈ next.config.cut.completed ↔ event ∈ state.config.cut.completed := by
  obtain ⟨completed, addressed, completedActor⟩ :=
    handle_event_actor runtime state next message accepted
  obtain ⟨stepped, steppedAddress, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  have same : stepped = completed := Option.some.inj (steppedAddress.symm.trans addressed)
  subst stepped
  have other : event ≠ completed := by
    intro same
    subst event
    rw [completedActor] at actor
    exact different (Option.some.inj actor.symm)
  rw [EventGraph.Config.step_cut state.config _ ready action next.config member,
    EventOrder.Cut.mem_complete]
  simp [other]

/-- A focal private command cannot alter the state attached to an event owned
by another player.  The candidate clause is deliberately restricted to the
canonical event slot needed by event-boundary arguments. -/
theorem privateStep_opponent_event
    (state : State graph) (focal owner : Player) (different : owner ≠ focal)
    (event : graph.EventId) (actor : graph.actor? event = some owner)
    (command : PrivateCommand graph) :
    (privateStep state focal command).remembered event = state.remembered event ∧
      (privateStep state focal command).candidates.lookup (owner, eventSlot event) =
        state.candidates.lookup (owner, eventSlot event) ∧
      (privateStep state focal command).accepted (.inr event) =
        state.accepted (.inr event) ∧
      (event ∈ (privateStep state focal command).config.cut.completed ↔
        event ∈ state.config.cut.completed) := by
  cases command with
  | prepare serial raw =>
      refine ⟨rfl, ?_, rfl, Iff.rfl⟩
      apply CommitmentCandidates.lookup_prepare_other
      intro same
      exact different (congrArg Prod.fst same)
  | remember changed action =>
      by_cases owned : graph.actor? changed = some focal
      · rw [privateStep, dif_pos owned]
        cases cached : state.remembered changed with
        | some prior => exact ⟨rfl, rfl, rfl, Iff.rfl⟩
        | none =>
            have notSame : event ≠ changed := by
              intro same
              subst changed
              rw [actor] at owned
              exact different (Option.some.inj owned)
            simp [Function.update_of_ne notSame]
      · rw [privateStep, dif_neg owned]
        exact ⟨rfl, rfl, rfl, Iff.rfl⟩

/-- The exact execution produced by a focal private command preserves both an
opponent's authenticated history and all native state attached to the
opponent-owned event. -/
theorem afterPrivate_opponent_event
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (focal owner : Player) (different : owner ≠ focal)
    (event : graph.EventId) (actor : graph.actor? event = some owner)
    (command : PrivateCommand graph) :
    (runtime.application.afterPrivate execution focal command).principalHistory owner =
        execution.principalHistory owner ∧
      (runtime.application.afterPrivate execution focal command).native.application.remembered
          event = execution.native.application.remembered event ∧
      CommitmentCandidates.lookup
          (runtime.application.afterPrivate execution focal command).native.application.candidates
          (owner, eventSlot event) =
        execution.native.application.candidates.lookup (owner, eventSlot event) ∧
      (runtime.application.afterPrivate execution focal command).native.application.accepted
          (.inr event) = execution.native.application.accepted (.inr event) ∧
      (event ∈
          (EventGraph.Config.cut (State.config
            (runtime.application.afterPrivate execution focal
              command).native.application)).completed ↔
        event ∈ execution.native.application.config.cut.completed) := by
  have frame := privateStep_opponent_event execution.native.application focal owner different
    event actor command
  simp only [MessageApplication.afterPrivate, different, ↓reduceIte]
  exact ⟨trivial, frame.1, frame.2.1, frame.2.2.1, frame.2.2.2⟩

/-- Submission changes only the focal player's history and the public message
pool.  In particular it cannot consume or mutate any opponent event state. -/
theorem afterSubmit_opponent_event
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (focal owner : Player) (different : owner ≠ focal)
    (event : graph.EventId) (payload : Payload graph) :
    (runtime.application.afterSubmit execution focal payload).principalHistory owner =
        execution.principalHistory owner ∧
      (runtime.application.afterSubmit execution focal payload).native.application.remembered
          event = execution.native.application.remembered event ∧
      CommitmentCandidates.lookup
          (runtime.application.afterSubmit execution focal payload).native.application.candidates
          (owner, eventSlot event) =
        execution.native.application.candidates.lookup (owner, eventSlot event) ∧
      (runtime.application.afterSubmit execution focal payload).native.application.accepted
          (.inr event) = execution.native.application.accepted (.inr event) ∧
      (event ∈
          (EventGraph.Config.cut (State.config
            (runtime.application.afterSubmit execution focal
              payload).native.application)).completed ↔
        event ∈ execution.native.application.config.cut.completed) := by
  simp [MessageApplication.afterSubmit, different]

end Vegas.EventGraphRuntime
