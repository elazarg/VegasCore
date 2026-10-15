/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceProgress
import Vegas.Pending.PhaseSeedCalendar

/-! # Exact physical clock changes of the phase calendar

Private responses, packet inclusion, activation, expiry and sampling preserve
the physical clock. Only the existing advanceClock environment command adds a
tick, including when normalization installs a new phase or retry namespace.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

theorem handle_clock (runtime : EventGraphRuntime graph) {inputs : graph.Inputs}
    (state next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (valid : state.Invariant inputs) (accepted : state.handle runtime message = some next) :
    next.current.native.clock = state.current.native.clock := by
  unfold handle at accepted
  split at accepted
  · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    change (settle _ _ _ _ _).current.native.clock = _
    rw [(settle_physical _ _ _ _ _).2.2]
    have clock := (EventGraphRuntime.handle_progress runtime inputs state.current.native native
      ⟨message.id, message.payload.packet.call⟩ valid.active handled).clock
    simpa only [RecoveryState.inclusionResult, Nat.add_zero] using clock
  · cases accepted

theorem environment_clock (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (command : EnvironmentCommand graph)
    (reached : next ∈ (state.environment runtime command).support) :
    next.current.native.clock = state.current.native.clock + command.clockTicks := by
  unfold environment at reached
  split at reached
  · obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    change (settle _ _ _ _ _).current.native.clock = _
    rw [(settle_physical _ _ _ _ _).2.2]
    exact environmentStep_clock runtime state.current.native native command moved
  · rename_i disallowed
    cases (PMF.mem_support_pure_iff _ _).mp reached
    cases command with
    | advanceClock => simp [commandAllowed] at disallowed
    | executeSample event => rfl
    | expire event => rfl

end PhaseRuntimeState

namespace PhaseSeedCalendar

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def commandTicks : (app).Command → Nat
  | .application command => command.clockTicks
  | _ => 0

/-- An arbitrary player's atomic response never advances the physical clock. -/
theorem respond_clock {inputs : graph.Inputs} (execution : (app).Execution)
    (valid : execution.application.Invariant inputs) (who : Player) (action : (app).Action) :
    (execution.respond app who action).application.current.native.clock =
      execution.application.current.native.clock := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      exact (execution.application.submit_progress who submission valid.active).clock.trans
        (Nat.add_zero _)

/-- Exact tick accounting uses the genuine environmentStep law and retains the
same clock even when packet handling closes or rolls back an attempt. -/
theorem environmentStep_clock {inputs : graph.Inputs}
    (execution next : (app).Execution) (command : (app).Command)
    (valid : execution.application.Invariant inputs)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.application.current.native.clock = execution.application.current.native.clock +
      commandTicks runtime leaks command := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | activate owner =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ reached
      rfl
  | application native =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
      obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ reached
      exact PhaseRuntimeState.environment_clock runtime execution.application state native moved
  | «include» identifier =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      simp only [ReactiveApplication.Execution.includePending]
      cases included : execution.network.includePending identifier with
      | mk envelope network =>
          cases envelope with
          | none => rfl
          | some message =>
              change ((execution.application.handle runtime message).getD
                execution.application).current.native.clock =
                  execution.application.current.native.clock + 0
              cases accepted : execution.application.handle runtime message with
              | none => simp only [Option.getD_none, Nat.add_zero]
              | some state =>
                  simp only [Option.getD_some, Nat.add_zero]
                  exact PhaseRuntimeState.handle_clock runtime execution.application state message
                    valid accepted

end PhaseSeedCalendar
end Vegas.EventGraphRuntime
