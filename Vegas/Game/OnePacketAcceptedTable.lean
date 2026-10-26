/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketReplayExists

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

/-- An accepted commitment completes its ready event, which had no accepted
handle, and installs its handle there. -/
theorem handle_commitment_accepted (state next : EventGraphRuntime.State (graph setup))
    (id : MessageId Player) (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    state.config.cut.Ready event ∧ state.accepted (.inr event) = none ∧
      next.accepted = Function.update state.accepted (.inr event) (some candidate) ∧
      event ∈ next.config.cut.completed := by
  obtain ⟨_, ready, owner, payload, outputEq, codeEq, _, configEq⟩ :=
    handle_commitment_action (runtime := runtime) state next id event candidate accepted
  have tables := handle_commitment_tables runtime state next id event candidate accepted
  refine ⟨ready, ?_, tables.2.1, ?_⟩
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView (graph setup) event with
      | resolve | sample => simp [handle, ready, timely, view] at accepted
      | bind owner' payload' outputEq' codeEq' =>
          simp only [handle, dite_eq_left ready, dite_eq_left timely, view] at accepted
          split at accepted
          · split at accepted
            · split at accepted
              · rename_i vacant
                exact vacant
              · cases accepted
            · cases accepted
          · cases accepted
    · simp [handle, ready, timely] at accepted
  · rw [configEq]
    exact (EventOrder.Cut.mem_complete _ _ ready _).mpr (Or.inl rfl)

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
    have call := reactiveHandle_call accepted
    cases packet : message.payload.call with
    | malformed raw =>
        rw [packet] at call
        simp [handle] at call
    | opening named candidate raw =>
        rw [packet] at call
        have tables := handle_resolution_tables runtime state next _
          (fun _ _ same => by cases same) call
        exact Or.inl (by rw [tables.1])
    | commitment named candidate =>
        rw [packet] at call
        obtain ⟨ready, vacant, table, completed⟩ :=
          handle_commitment_accepted (runtime := runtime) state next message.id named candidate call
        by_cases same : event = named
        · subst same
          exact Or.inr ⟨ready, vacant, completed⟩
        · refine Or.inl ?_
          rw [table, Function.update_of_ne]
          exact fun equal => same (Sum.inr.inj equal)
  environment state command next reached event :=
    Or.inl (by rw [(environmentStep_tables runtime state next command reached).1])

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
  rcases transition_configStep (initialLaw setup) horizon scheduler before
    after joint reached with
    same | ⟨other, ready, action, member⟩
  · rw [same]
    exact completed
  · rw [before.execution.application.config.step_cut other ready action _ member,
      EventOrder.Cut.mem_complete]
    exact Or.inr completed

/-- **Accepted events have completed** along every history of the one-packet
game. -/
theorem accepted_completed : ∀ {state}
    (_ : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (control : (application setup runtime leaks).Control), state = some control →
    ∀ event, control.execution.application.accepted (.inr event) ≠ none →
      event ∈ control.execution.application.config.cut.completed
  | _, .start, _, current, _, _ => by cases current
  | _, .extend (source := before) prior joint _ realized, control, current, event, present => by
      have recursive := fun next same => accepted_completed prior next same
      subst current
      change some control ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
        scheduler before joint).support at realized
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup runtime leaks)
              state⟩ : (application setup runtime leaks).Control)).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          exfalso
          apply present
          cases found : (EventGraphRuntime.State.initial (graph := graph setup)
              (setup.eventInputs initial)).accepted (.inr event) with
          | none => rfl
          | some handle =>
              obtain ⟨_, _, _, impossible, _⟩ := State.initial_accepted_eq_some _ _ handle found
              cases impossible
      | some current =>
          rcases acceptedKept_transition (runtime := runtime) leaks (initialLaw setup) horizon
            scheduler current control
              joint realized event with same | ⟨_, _, completed⟩
          · rw [same] at present
            exact completed_transition (runtime := runtime) leaks joint realized (recursive
              current rfl event present)
          · exact completed

end Vegas
