/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionInvariant
import Vegas.Pending.EventProgress
import Vegas.Pending.ExclusionProjection
import Vegas.Pending.ReactiveServiceProgress
import Interaction.ReactiveServiceRounds
import Interaction.ReactivePolicyInvariant

/-! # Native progress through permanent-exclusion recovery -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

omit [DecidableEq Player] in
theorem completeFailure_progress {inputs : graph.Inputs} (state : State graph)
    (valid : state.Invariant inputs) (event : graph.EventId)
    (ready : state.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    ServiceProgress inputs 0 state (state.completeFailure event ready) := by
  obtain ⟨action, supported⟩ := state.completeFailure_step event ready acting
  refine ⟨completeFailure_invariant valid event ready acting,
    completed_subset_of_mem_step _ _ ready action _ supported, ?_, ?_⟩
  · simpa only [Nat.add_zero] using (state.completeFailure_tables event ready).2.2
  · intro query entered activated unfinished
    have stable := valid.refreshStep_activatedAt_of_not_completed event query ready action
      (state.completeFailure event ready).config supported entered activated unfinished
    cases view : nodeView graph event with
    | bind actor payload outputEq codeEq =>
        simpa only [completeFailure, view, complete] using stable
    | resolve actor payload binding checks outputEq codeEq =>
        simpa only [completeFailure, view, complete] using stable
    | sample payload law outputEq codeEq =>
        have actorEq : graph.actor? event = none :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        rw [actorEq] at acting
        cases acting

end State

namespace RecoveryState

theorem drainFuel_progress (fuel : Nat) (state : RecoveryState graph)
    {inputs : graph.Inputs} (valid : state.native.Invariant inputs) :
    State.ServiceProgress inputs 0 state.native (state.drainFuel fuel).native := by
  apply drainFuel_induction
    (fun next => State.ServiceProgress inputs 0 state.native next.native)
    (fun before event eligible previous => ?_) fuel state (.refl valid)
  obtain ⟨owner, acting, _⟩ := eligible.owned
  have last := before.native.completeFailure_progress previous.invariant event eligible.1 acting
  change State.ServiceProgress inputs 0 state.native
    (before.native.completeFailure event eligible.1)
  simpa only [Nat.zero_add] using previous.trans last

theorem drain_progress (state : RecoveryState graph)
    {inputs : graph.Inputs} (valid : state.native.Invariant inputs) :
    State.ServiceProgress inputs 0 state.native state.drain.native :=
  drainFuel_progress _ state valid

theorem handle_progress (runtime : EventGraphRuntime graph) (state next : RecoveryState graph)
    (message : Message Player (WitnessedPacket graph)) {inputs : graph.Inputs}
    (valid : state.native.Invariant inputs) (accepted : state.handle runtime message = some next) :
    State.ServiceProgress inputs 0 state.native next.native := by
  unfold handle at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have first := EventGraphRuntime.handle_progress runtime inputs state.native native
        ⟨message.id, message.payload.call⟩ valid handled
      have last := (state.inclusionResult message.payload.call native).drain_progress
        first.invariant
      simpa only [Nat.zero_add] using first.trans last
    · cases accepted

theorem environment_progress (runtime : EventGraphRuntime graph) (state next : RecoveryState graph)
    (command : EnvironmentCommand graph) {inputs : graph.Inputs}
    (valid : state.native.Invariant inputs)
    (reached : next ∈ (state.environment runtime command).support) :
    State.ServiceProgress inputs command.clockTicks state.native next.native := by
  rw [environment, PMF.support_map] at reached
  obtain ⟨native, moved, rfl⟩ := reached
  have first : State.ServiceProgress inputs command.clockTicks state.native native :=
    ⟨environmentStep_invariant runtime state.native native command valid moved,
      environmentStep_completed_subset runtime state.native native command moved,
      environmentStep_clock runtime state.native native command moved,
      environmentStep_activatedAt_of_not_completed runtime state.native native command valid moved⟩
  have last := (state.environmentResult command native).drain_progress first.invariant
  simpa only [Nat.add_zero] using first.trans last

theorem expire_complete (runtime : EventGraphRuntime graph) (state next : RecoveryState graph)
    {inputs : graph.Inputs} (valid : state.native.Invariant inputs) (event : graph.EventId)
    (ready : state.native.config.cut.Ready event) (strategic : (graph.actor? event).isSome = true)
    (entered : Nat) (activated : state.native.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.native.clock - entered)
    (reached : next ∈ (state.environment runtime (.expire event)).support) :
    event ∈ next.native.config.cut.completed := by
  rw [environment, PMF.support_map] at reached
  obtain ⟨native, moved, rfl⟩ := reached
  have completed := environmentStep_expire_complete runtime state.native native event ready
    strategic entered activated due moved
  have validNative := environmentStep_invariant runtime state.native native (.expire event)
    valid moved
  exact ((state.environmentResult (.expire event) native).drain_progress validNative).completed
    completed

end RecoveryState

theorem recoveryApplication_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) :
    (recoveryApplication runtime leaks).Invariant (RecoveryState.Invariant inputs) where
  submit _ who submission valid := valid.submit who submission
  handle _ message next valid accepted := valid.handle runtime message next accepted
  environment _ native next valid moved := valid.environment runtime native next moved

namespace Recovery

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => recoveryApplication runtime leaks

def commandTicks : (app).Command → Nat
  | .application native => native.clockTicks
  | _ => 0

theorem respond_progress (inputs : graph.Inputs) (execution : (app).Execution) (who : Player)
    (action : (app).Action) (valid : execution.application.native.Invariant inputs) :
    State.ServiceProgress inputs 0 execution.application.native
      (execution.respond app who action).application.native := by
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact .refl valid
      | some material =>
          exact runtime.reactive_respond_progress leaks inputs
            (RecoveryProjection.execution runtime leaks execution) who ⟨some material⟩ valid

theorem include_progress (inputs : graph.Inputs) (execution : (app).Execution)
    (identifier : MessageId Player) (valid : execution.application.native.Invariant inputs) :
    State.ServiceProgress inputs 0 execution.application.native
      (execution.includePending app identifier).application.native := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup identifier with
  | none => exact .refl valid
  | some message =>
      change State.ServiceProgress inputs 0 execution.application.native
        ((execution.application.handle runtime message).getD execution.application).native
      cases accepted : execution.application.handle runtime message with
      | none => exact .refl valid
      | some next =>
          exact execution.application.handle_progress runtime next message valid accepted

theorem environmentStep_progress (inputs : graph.Inputs) (execution next : (app).Execution)
    (command : (app).Command) (valid : execution.application.native.Invariant inputs)
    (reached : next ∈ (execution.environmentStep app command).support) :
    State.ServiceProgress inputs (commandTicks runtime leaks command)
      execution.application.native next.application.native := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at reached
      cases reached
      exact .refl valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact .refl valid
  | «include» identifier =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at reached
      cases reached
      exact include_progress runtime leaks inputs execution identifier valid
  | application native =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ supported
      exact execution.application.environment_progress runtime state native valid moved

theorem runRounds_progress (inputs : graph.Inputs) (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (before after : (app).Execution)
    (valid : before.application.native.Invariant inputs)
    (reached : after ∈ ((app).runRounds scheduler players count before).support) :
    ∃ ticks, State.ServiceProgress inputs ticks before.application.native
      after.application.native := by
  let predicate := fun execution : (app).Execution =>
    ∃ ticks, State.ServiceProgress inputs ticks before.application.native
      execution.application.native
  have invariant : (app).PolicyInvariant players predicate := {
    respond := by
      intro execution who action previous _
      obtain ⟨ticks, previous⟩ := previous
      exact ⟨_, previous.trans (respond_progress runtime leaks inputs execution who action
        previous.invariant)⟩
    environment := by
      intro execution next command previous moved
      obtain ⟨ticks, previous⟩ := previous
      exact ⟨_, previous.trans (environmentStep_progress runtime leaks inputs execution next
        command previous.invariant moved)⟩ }
  exact invariant.runRounds scheduler count before after ⟨0, .refl valid⟩ reached

end Recovery
end Vegas.EventGraphRuntime
