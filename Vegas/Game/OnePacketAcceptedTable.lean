/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFactorization
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveGraphSteps

/-! # The public table of accepted binding handles

The contract's table of accepted handles is public. The handle accepted at an
event's output changes only when that event, ready and with no accepted
handle, is completed by an accepted commitment (`Vegas.acceptedKept_step`).
Hence along every history of the one-packet game an event with an accepted
handle has completed (`Vegas.accepted_completed`), a completed event without an
accepted handle never acquires one, and an accepted handle is never removed
(`Vegas.acceptedKept_transition`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}

variable (setup runtime) in
/-- The accepted handle of every event output is kept, except at an event that
was ready with none and has completed. -/
def AcceptedKept (before after : EventGraphRuntime.State (graph setup)) : Prop :=
  ∀ event, after.accepted (.inr event) = before.accepted (.inr event) ∨
    (before.config.cut.Ready event ∧ before.accepted (.inr event) = none ∧
      event ∈ after.config.cut.completed)

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- **Accepted handles change only at their own completion.** -/
theorem acceptedKept_step :
    (runtime.reactiveApplication leaks).StepRelation (AcceptedKept setup) where
  refl _ _ := Or.inl rfl
  submit state who material event := Or.inl (by
    change (submitStep (material.call.register state who) who
      material.call.packet).accepted (.inr event) = _
    rw [submitStep_accepted, Submission.register_accepted])
  handle state message next accepted event := by
    obtain ⟨native, call, rfl⟩ := reactiveHandle_call accepted
    rw [native.drain_tables.1]
    cases packet : message.payload.call with
    | malformed raw =>
        rw [packet] at call
        simp [handle] at call
    | opening named candidate raw =>
        rw [packet] at call
        have tables := handle_resolution_tables runtime state native _
          (fun _ _ same => by cases same) call
        exact Or.inl (by rw [tables.1])
    | commitment named candidate =>
        rw [packet] at call
        obtain ⟨ready, vacant, table, completed⟩ :=
          handle_commitment_accepted runtime state native message.id named candidate call
        by_cases same : event = named
        · subst same
          exact Or.inr ⟨ready, vacant,
            EventGraph.Config.Step.path_completed_mono native.drain_graph_steps completed⟩
        · refine Or.inl ?_
          rw [table, Function.update_of_ne]
          exact fun equal => same (Sum.inr.inj equal)
  environment state command next reached event :=
    Or.inl (by rw [(runtime.reactiveApplication_environment_tables leaks state next
      command reached).1])

/-- Every transition of the supplied runtime keeps accepted handles except at the
completed event. -/
theorem acceptedKept_transition (initial : PMF (application setup runtime leaks).State) (horizon :
  Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (before after : (application setup runtime leaks).Control)
    (joint : Player → Option (application setup runtime leaks).Action)
    (reached : some after ∈ ((application setup runtime leaks).transition initial horizon scheduler
      (some before) joint).support) :
    AcceptedKept setup before.execution.application after.execution.application :=
  (acceptedKept_step (runtime := runtime) leaks).transition initial horizon scheduler before after
    joint reached

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

omit [Fintype Player] in
/-- Completed events stay completed along a transition. -/
theorem completed_transition {before after : (application setup runtime leaks).Control}
    (joint : Player → Option (application setup runtime leaks).Action)
    (reached : some after ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler (some before) joint).support) {event : (graph setup).EventId}
    (completed : event ∈ before.execution.application.config.cut.completed) :
    event ∈ after.execution.application.config.cut.completed := by
  exact EventGraph.Config.Step.path_completed_mono
    (runtime.reactive_protocol_graph_steps leaks (initialLaw setup) horizon scheduler before
      after joint reached) completed

/-- **Accepted events have completed** along every history of the one-packet
game. -/
theorem accepted_completed {state}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (control : (application setup runtime leaks).Control) (current : state = some control)
    (event : (graph setup).EventId)
    (present : control.execution.application.accepted (.inr event) ≠ none) :
    event ∈ control.execution.application.config.cut.completed := by
  subst current
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace
    (initialLaw setup) horizon scheduler trace
  have valid : control.execution.application.BindingInvariant :=
    (runtime.reactiveBindingInvariant leaks).history (initialLaw setup) horizon
      scheduler (fun state member => by
        obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
        exact State.initial_bindingInvariant _) rawTrace
  cases accepted : control.execution.application.accepted (.inr event) with
  | none => exact (present accepted).elim
  | some candidate =>
      exact valid.toAssociationInvariant.accepted_complete event candidate accepted

end Vegas
