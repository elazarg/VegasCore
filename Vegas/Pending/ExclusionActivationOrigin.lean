/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionServiceProgress
import Vegas.Pending.ReactiveServiceOpportunity

/-! # Activation origins across permanent-exclusion service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RecoveryState

theorem drainFuel_activationOrigin (fuel : Nat) (state : RecoveryState graph)
    {inputs : graph.Inputs} (valid : state.native.Invariant inputs) :
    State.ActivationOrigin state.native (state.drainFuel fuel).native := by
  induction fuel generalizing state with
  | zero => exact State.activationOrigin_of_activatedEq rfl
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        have eligible := Classical.choose_spec pending
        obtain ⟨owner, acting, _⟩ := eligible.owned
        have first := State.activationOrigin_of_refreshEq
          (state.native.completeFailure_activated _ eligible.1 acting)
        have progress := state.native.completeFailure_progress valid _ eligible.1 acting
        have later := (state.completeAutomatic _ eligible).drainFuel_progress fuel
          progress.invariant
        exact first.trans (ih _ progress.invariant) (by rw [progress.clock]; omega)
          later.completed
      · exact State.activationOrigin_of_activatedEq rfl

theorem drain_activationOrigin (state : RecoveryState graph)
    {inputs : graph.Inputs} (valid : state.native.Invariant inputs) :
    State.ActivationOrigin state.native state.drain.native :=
  drainFuel_activationOrigin _ state valid

theorem handle_activationOrigin (runtime : EventGraphRuntime graph)
    (state next : RecoveryState graph) (message : Message Player (WitnessedPacket graph))
    {inputs : graph.Inputs} (valid : state.native.Invariant inputs)
    (accepted : state.handle runtime message = some next) :
    State.ActivationOrigin state.native next.native := by
  unfold handle at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have first := State.activationOrigin_of_refreshEq
        (handle_clock_activated runtime state.native native ⟨message.id, message.payload.call⟩
          handled).2
      have progress := EventGraphRuntime.handle_progress runtime inputs state.native native
        ⟨message.id, message.payload.call⟩ valid handled
      have later := (state.inclusionResult message.payload.call native).drain_progress
        progress.invariant
      exact first.trans
        ((state.inclusionResult message.payload.call native).drain_activationOrigin
          progress.invariant) (by rw [progress.clock]; omega) later.completed
    · cases accepted

end RecoveryState

namespace Recovery

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => recoveryApplication runtime leaks

theorem respond_activationOrigin (execution : (app).Execution) (who : Player)
    (action : (app).Action) :
    State.ActivationOrigin execution.application.native
      (execution.respond app who action).application.native := by
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact State.activationOrigin_of_activatedEq rfl
      | some material =>
          exact ((reactiveActivationStart runtime leaks).submit execution.application.native
            who material).activationOrigin

theorem environmentStep_activationOrigin (inputs : graph.Inputs)
    (execution next : (app).Execution) (command : (app).Command)
    (valid : execution.application.native.Invariant inputs)
    (reached : next ∈ (execution.environmentStep app command).support) :
    State.ActivationOrigin execution.application.native next.application.native := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at reached
      cases reached
      exact State.activationOrigin_of_activatedEq rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact State.activationOrigin_of_activatedEq rfl
  | «include» identifier =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at reached
      cases reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup identifier with
      | none => exact State.activationOrigin_of_activatedEq rfl
      | some message =>
          change State.ActivationOrigin execution.application.native
            ((execution.application.handle runtime message).getD execution.application).native
          cases accepted : execution.application.handle runtime message with
          | none => exact State.activationOrigin_of_activatedEq rfl
          | some next =>
              exact execution.application.handle_activationOrigin runtime next message valid
                accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (execution.application.environment runtime command).support at moved
      rw [RecoveryState.environment, PMF.support_map] at moved
      obtain ⟨native, moved, rfl⟩ := moved
      have first := ((reactiveActivationStart runtime leaks).environment
        execution.application.native command native moved).activationOrigin
      have nativeClock := environmentStep_clock runtime execution.application.native native
        command moved
      have validNative := environmentStep_invariant runtime execution.application.native native
        command valid moved
      have later := (execution.application.environmentResult command native).drain_progress
        validNative
      exact first.trans
        ((execution.application.environmentResult command native).drain_activationOrigin
          validNative)
        (by rw [nativeClock]; omega) later.completed

end Recovery
end Vegas.EventGraphRuntime
