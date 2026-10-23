/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseResolution

/-! # Native service progress inside one physical phase namespace

Existing native service progress transports through automatic phase completion
whenever normalization keeps the namespace. This supplies the original ready
clock and irreversible completion facts used by the finite calendar argument.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

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

namespace RuntimePhase

theorem drainFuel_progress (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) {inputs : graph.Inputs} (valid : state.native.Invariant inputs) :
    State.ServiceProgress inputs 0 state.native (phase.drainFuel fuel state).native := by
  induction fuel generalizing state with
  | zero => exact .refl valid
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        have eligible := (Classical.choose_spec pending).2
        obtain ⟨owner, acting, _⟩ := eligible.owned
        have first := state.native.completeFailure_progress valid _ eligible.1 acting
        simpa only [Nat.zero_add] using first.trans
          (ih (state.completeAutomatic (Classical.choose pending) eligible) first.invariant)
      · exact .refl valid

theorem drain_progress (phase : RuntimePhase graph) (state : RecoveryState graph)
    {inputs : graph.Inputs} (valid : state.native.Invariant inputs) :
    State.ServiceProgress inputs 0 state.native (phase.drain state).native :=
  drainFuel_progress phase _ state valid

end RuntimePhase

namespace PhaseRuntimeState

/-- Native clock and ready-time progress is unchanged by phase closure when no
physical namespace is retired. -/
theorem normalize_progress {inputs : graph.Inputs} (state : PhaseRuntimeState graph)
    (valid : state.current.native.Invariant inputs) (ordered : state.Ordered)
    (same : state.attempt = state.normalize.attempt) :
    State.ServiceProgress inputs 0 state.current.native state.normalize.current.native := by
  have settled := settle_of_same_namespace state.phases state.generation state.entry
    state.current state.retired ordered same
  have currentEq := congrArg PhaseRuntimeState.current settled
  change State.ServiceProgress inputs 0 state.current.native
    (settle state.phases state.generation state.entry state.current state.retired).current.native
  rw [currentEq]
  cases phases : state.phases with
  | nil => exact .refl valid
  | cons phase remaining => exact phase.drain_progress state.current valid

/-- Private preparation and emission preserve the native cut, clock and event
activation table exactly; full physical recall is handled by the existing app. -/
theorem submit_progress {inputs : graph.Inputs} (state : PhaseRuntimeState graph)
    (who : Player) (submission : WitnessedSubmission graph)
    (valid : state.current.native.Invariant inputs) :
    State.ServiceProgress inputs 0 state.current.native
      (state.submit who submission).current.native := by
  have configEq : (state.submit who submission).current.native.config =
      state.current.native.config := by
    change (submitStep (submission.call.register state.current.native who)
      who submission.call.packet).config = _
    rw [submitStep_config, (submission.call.register_facts who state.current.native).1]
  have publicEq := (submitStep_publicView
    (submission.call.register state.current.native who) who submission.call.packet).trans
      (submission.call.register_facts who state.current.native).2
  have clockEq : (state.submit who submission).current.native.clock = state.current.native.clock :=
    congrArg PublicView.clock publicEq
  have activatedEq : (state.submit who submission).current.native.activatedAt =
      state.current.native.activatedAt := congrArg PublicView.activatedAt publicEq
  refine ⟨valid.copy configEq clockEq activatedEq, ?_, ?_, ?_⟩
  · rw [configEq]
  · simpa only [Nat.add_zero] using clockEq
  · intro event entered activated _
    rwa [activatedEq]

/-- An accepted actual packet makes native service progress whenever its
normalization retains the packet's physical namespace. -/
theorem handle_progress_of_same_namespace (runtime : EventGraphRuntime graph)
    {inputs : graph.Inputs} (state next : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph)) (valid : state.Invariant inputs)
    (ordered : state.Ordered) (accepted : state.handle runtime message = some next)
    (same : state.attempt = next.attempt) :
    State.ServiceProgress inputs 0 state.current.native next.current.native := by
  unfold handle at accepted
  split at accepted
  · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have first := EventGraphRuntime.handle_progress runtime inputs state.current.native native
      ⟨message.id, message.payload.packet.call⟩ valid.active handled
    have second := normalize_progress
      ({ state with current := state.current.inclusionResult message.payload.packet.call native } :
        PhaseRuntimeState graph) first.invariant ordered same
    simpa only [Nat.zero_add] using first.trans second
  · cases accepted

/-- Actual clock/sample/expiry commands preserve the original ready-time stamp
until completion, as long as no automatic retry retires the namespace. -/
theorem environment_progress_of_same_namespace (runtime : EventGraphRuntime graph)
    {inputs : graph.Inputs} (state next : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph) (valid : state.Invariant inputs) (ordered : state.Ordered)
    (reached : next ∈ (state.environment runtime command).support)
    (same : state.attempt = next.attempt) :
    State.ServiceProgress inputs command.clockTicks state.current.native next.current.native := by
  unfold environment at reached
  split at reached
  · obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    have first : State.ServiceProgress inputs command.clockTicks state.current.native native :=
      ⟨environmentStep_invariant runtime _ _ command valid.active moved,
        environmentStep_completed_subset runtime _ _ command moved,
        environmentStep_clock runtime _ _ command moved,
        fun event entered activated unfinished => environmentStep_activatedAt_of_not_completed
          runtime _ _ command valid.active moved event entered activated unfinished⟩
    have second := normalize_progress
      ({ state with current := state.current.environmentResult command native } :
        PhaseRuntimeState graph) first.invariant ordered same
    simpa only [Nat.add_zero] using first.trans second
  · rename_i disallowed
    cases (PMF.mem_support_pure_iff _ _).mp reached
    cases command with
    | advanceClock => simp [commandAllowed] at disallowed
    | executeSample event => exact .refl valid.active
    | expire event => exact .refl valid.active

end PhaseRuntimeState
/-- The existing actual execution interface inherits native ready-clock
stability between two states in the same physical attempt. -/
theorem phaseApplication_serviceProgress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      ∀ inputs, before.Invariant inputs → before.Ordered → before.attempt = after.attempt →
        ∃ ticks, State.ServiceProgress inputs ticks
          before.current.native after.current.native) where
  refl _state _ valid _ _ := ⟨0, .refl valid.active⟩
  submit state who submission _ valid _ _ :=
    ⟨0, state.submit_progress who submission valid.active⟩
  handle state message next accepted _ valid ordered same :=
    ⟨0, state.handle_progress_of_same_namespace runtime next message valid ordered accepted same⟩
  environment state command next reached _ valid ordered same :=
    ⟨command.clockTicks,
      state.environment_progress_of_same_namespace runtime next command valid ordered reached same⟩

end Vegas.EventGraphRuntime
