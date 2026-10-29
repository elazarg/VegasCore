/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveService
import Vegas.Pending.EventProgress
import Vegas.Pending.ExclusionInvariant

/-! # Progress under arbitrary reactive player and network policies

The service advances the application clock only at explicit ticks. Player
responses and network choices preserve completed events and live activation
times. These laws do not assume prescribed behavior or successful inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Zero-time automatic completions preserve established service progress. -/
theorem State.ServiceProgress.drain {inputs : graph.Inputs} {ticks : Nat}
    {before after : State graph} (progress : State.ServiceProgress inputs ticks before after) :
    State.ServiceProgress inputs ticks before after.drain := by
  have completed := State.drainFuel_completed_subset after.config.remaining after
  refine ⟨progress.invariant.drain, progress.completed.trans completed,
    after.drain_tables.2.2.trans progress.clock, ?_⟩
  intro event entered activated unfinished
  exact progress.invariant.drain_activatedAt_of_not_completed event entered
    (progress.activated event entered activated (fun done => unfinished (completed done)))
    unfinished

/-- Automatic completion after an accepted call preserves the clock. -/
theorem reactiveApplication_handle_clock (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (message : Message Player (WitnessedPacket graph))
    (accepted : (runtime.reactiveApplication leaks).handle state message = some next) :
    next.clock = state.clock := by
  obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
  rw [← nextEq, native.drain_tables.2.2]
  exact (handle_clock_activated runtime state native ⟨message.id, message.payload.call⟩ handled).1

/-- Application time advances only by the native command's explicit ticks. -/
theorem reactiveApplication_environment_clock (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (command : EnvironmentCommand graph)
    (supported : next ∈ ((runtime.reactiveApplication leaks).environment state command).support) :
    next.clock = state.clock + command.clockTicks := by
  change next ∈ ((environmentStep runtime state command).map State.drain).support at supported
  obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ supported
  rw [native.drain_tables.2.2]
  exact environmentStep_clock runtime state native command moved

theorem reactive_respond_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs)
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action)
    (invariant : execution.application.Invariant inputs) :
    State.ServiceProgress inputs 0 execution.application
      (execution.respond (runtime.reactiveApplication leaks) who action).application := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact .refl invariant
  | some submission =>
      change State.ServiceProgress inputs 0 execution.application
        (submitStep (submission.call.register execution.application who) who
          submission.call.packet)
      have facts := submission.call.register_facts who execution.application
      have publicEq : State.publicView
          (submitStep (submission.call.register execution.application who) who
            submission.call.packet) =
            execution.application.publicView := by
        rw [submitStep_publicView, facts.2]
      have configEq := (submitStep_config
        (submission.call.register execution.application who) who submission.call.packet).trans
          facts.1
      have clockEq := congrArg PublicView.clock publicEq
      have activationEq := congrArg PublicView.activatedAt publicEq
      dsimp only [State.publicView] at clockEq activationEq
      refine ⟨invariant.copy configEq clockEq activationEq, ?_, ?_, ?_⟩
      · rw [configEq]
      · simpa only [Nat.add_zero] using clockEq
      · intro event entered activated _
        rw [activationEq]
        exact activated

def reactiveTicks (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
      (runtime.reactiveApplication leaks).Command → Nat
  | .application .advanceClock => 1
  | _ => 0

/-- A player response never moves the clock. -/
theorem reactive_respond_clock (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    (execution.respond (runtime.reactiveApplication leaks) who action).application.clock =
      execution.application.clock := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      exact congrArg PublicView.clock
        (runtime.reactiveApplication_submit_publicView leaks execution.application who material)

/-- **Only explicit clock commands advance time.** Every scheduler command
moves the clock by its tick count: one for the application's `EnvironmentCommand.advanceClock`,
zero for activation, inclusion, waiting, sampling and expiry. No invariant is
assumed. -/
theorem reactive_environmentStep_clock (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    next.application.clock = execution.application.clock + runtime.reactiveTicks leaks command := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      change (execution.includePending (runtime.reactiveApplication leaks) id).application.clock =
        execution.application.clock + 0
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some message =>
          change (((runtime.reactiveApplication leaks).handle execution.application
            message).getD execution.application).clock = _
          cases accepted : (runtime.reactiveApplication leaks).handle execution.application
              message with
          | none => rfl
          | some state =>
              exact reactiveApplication_handle_clock runtime leaks execution.application state
                message accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      have clock := reactiveApplication_environment_clock runtime leaks execution.application
        state command changed
      cases command <;> simpa [reactiveTicks, EnvironmentCommand.clockTicks] using clock

theorem reactive_include_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs)
    (execution : (runtime.reactiveApplication leaks).Execution) (id : MessageId Player)
    (invariant : execution.application.Invariant inputs) :
    State.ServiceProgress inputs 0 execution.application
      (execution.includePending (runtime.reactiveApplication leaks) id).application := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact .refl invariant
  | some message =>
      change State.ServiceProgress inputs 0 execution.application
        (((runtime.reactiveApplication leaks).handle execution.application
          message).getD execution.application)
      cases accepted : (runtime.reactiveApplication leaks).handle execution.application
          message with
      | none => exact .refl invariant
      | some next =>
          obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
          rw [← nextEq]
          exact (handle_progress runtime inputs _ native
            ⟨message.id, message.payload.call⟩ invariant handled).drain

theorem reactive_environment_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (invariant : execution.application.Invariant inputs)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    State.ServiceProgress inputs (runtime.reactiveTicks leaks command)
      execution.application next.application := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact .refl invariant
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact .refl invariant
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact runtime.reactive_include_progress leaks inputs execution id invariant
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep runtime execution.application command).map
        State.drain).support at changed
      obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
      apply State.ServiceProgress.drain
      refine ⟨environmentStep_invariant runtime execution.application native
        command invariant moved,
        environmentStep_completed_subset runtime execution.application native command moved,
        ?_, ?_⟩
      · have clock := environmentStep_clock runtime execution.application native command moved
        cases command <;> simpa [reactiveTicks, EnvironmentCommand.clockTicks] using clock
      · exact environmentStep_activatedAt_of_not_completed runtime
          execution.application native command invariant moved

end Vegas.EventGraphRuntime
