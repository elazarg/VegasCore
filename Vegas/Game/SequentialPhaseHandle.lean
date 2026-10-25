/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseSettlement
import Vegas.Pending.PhaseCheckpointExclusion
import Vegas.Pending.PhaseClearService
import Vegas.Pending.PhaseLive
import Vegas.Pending.PhasePlanSuffix

/-! # Actual packet handling through the sequential singleton current projection

Native acceptance determines the active event, while the signed packet retains
its physical attempt. The projection compares actual handlers and complete
forced-exit states; it asserts no equivalence of archived player observations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

private theorem accepted_native_handle_current_sequential
    (runtime : EventGraphRuntime graph.sequentialize)
    (state : PhaseRuntimeState graph.sequentialize)
    (frontier : state.Frontier) (live : state.Live) (stored : state.StoredCheckpoint)
    (history : state.HistoryCheckpoint) (frame : state.AcceptedCheckpointFrame)
    (exclusions : state.ExclusionRecord)
    (singletons : ∀ phase ∈ state.phases, phase.high = phase.low + 1)
    (message : Message Player (CommitAttemptPacket graph.sequentialize))
    (native : State graph.sequentialize)
    (accepted : EventGraphRuntime.handle runtime state.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    state.allows message.payload.packet.call = true ∧
      ({ state with current := state.current.inclusionResult message.payload.packet.call native } :
        PhaseRuntimeState graph.sequentialize).normalize.current =
        (state.current.inclusionResult message.payload.packet.call native).drain := by
  obtain ⟨event, named, ready, action, supported⟩ :=
    handle_config_mem_step runtime state.current.native native _ accepted
  cases phases : state.phases with
  | nil =>
      have terminal := frontier.terminal phases
      exact (ready.1 (by rw [terminal]; exact Finset.mem_univ _)).elim
  | cons phase remaining =>
      have head : state.phases.head? = some phase := by rw [phases]; rfl
      have position := frontier.positioned
      rw [phases] at position
      have inside := phase.ready_mem_sequential state.current position.2
        (live phase (by rw [head]; rfl)) event ready
      have only : phase.events = {event} := by
        have singleton := phase.events_eq_singleton
          (singletons phase (by rw [phases]; exact List.mem_cons_self))
        have same := Finset.mem_singleton.mp ((Finset.ext_iff.mp singleton _).mp inside)
        rw [singleton, same]
      have allowed : state.allows message.payload.packet.call = true := by
        simp only [allows, head, named]
        exact decide_eq_true inside
      refine ⟨allowed, ?_⟩
      have aligned := state.checkpoint_eq_of_singleton_unfinished frontier stored history frame
        phase head event only ready.1
      have sameExcluded := exclusions.excluded_eq_of_same_config phase head aligned.1
      let after := state.current.inclusionResult message.payload.packet.call native
      have nextFrontier := frontier.after_effect after
        (Or.inr ⟨phase, by rw [head]; rfl, event, inside, ready, action, supported⟩)
      change (settle (phase :: remaining) state.generation state.entry after
        state.retired).current = after.drain
      by_cases unchanged : after.excluded = state.current.excluded
      · simpa only [phases] using
          settle_current_eq_drain_sequential state.phases state.generation state.entry after
            state.retired (sameExcluded.trans unchanged.symm) nextFrontier
      · cases call : message.payload.packet.call with
        | commitment actual candidate =>
            apply (unchanged ?_).elim
            dsimp only [after, RecoveryState.inclusionResult]
            rw [call]
        | malformed raw =>
            simp only [call, EventGraphRuntime.handle] at accepted
            cases accepted
        | opening actual candidate raw =>
            have same : actual = event := by
              rw [call] at named
              exact Option.some.inj named
            subst actual
            have opening := accepted
            rw [call] at opening
            obtain ⟨_ready, _timely, owner, payload, binding, checks, outputEq, codeEq,
              _value, _result, _view, _sender, _handleOwner, _associated, _raw, _verified,
              _stored, _resolved, _next⟩ :=
              (handle_opening_iff runtime state.current.native native message.id event candidate
                raw).mp opening
            have kind : phase.kind ≠ .commitment := by
              intro commitment
              have field := phase.fields event ((phase.mem_events event).mp inside).1
                ((phase.mem_events event).mp inside).2
              rw [commitment] at field
              obtain ⟨otherOwner, otherPayload, typed⟩ := field
              cases typed.symm.trans outputEq
            have completed : event ∈ after.native.config.cut.completed := by
              change event ∈ native.config.cut.completed
              rw [state.current.native.config.step_cut event ready action _ supported]
              simp
            exact settle_current_noncommit_singleton_eq_drain_sequential phase remaining
              state.generation state.entry after state.retired
              (by simpa only [phases] using nextFrontier) event only completed kind

/-- The original and phase handlers have the same complete current result when
any natively accepted packet retains the active attempt. Rejected native calls
need no attempt hypothesis. -/
theorem handle_current_sequential
    (runtime : EventGraphRuntime graph.sequentialize)
    (state : PhaseRuntimeState graph.sequentialize)
    (frontier : state.Frontier) (live : state.Live) (stored : state.StoredCheckpoint)
    (history : state.HistoryCheckpoint) (frame : state.AcceptedCheckpointFrame)
    (exclusions : state.ExclusionRecord)
    (singletons : ∀ phase ∈ state.phases, phase.high = phase.low + 1)
    (message : Message Player (CommitAttemptPacket graph.sequentialize))
    (attempt : ∀ native, EventGraphRuntime.handle runtime state.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native →
        message.payload.attempt = state.attempt) :
    (state.handle runtime message).map PhaseRuntimeState.current =
      state.current.handle runtime ⟨message.id, message.payload.packet⟩ := by
  cases raw : EventGraphRuntime.handle runtime state.current.native
      ⟨message.id, message.payload.packet.call⟩ with
  | none => simp only [handle, RecoveryState.handle, raw, Option.map_none, ite_self]
  | some native =>
      obtain ⟨allowed, current⟩ := accepted_native_handle_current_sequential runtime state frontier
        live stored history frame exclusions singletons message native raw
      have sameAttempt := attempt native raw
      cases excluded : state.current.excludedCall message.payload.packet.call <;>
        cases token : message.payload.packet.tokenValid <;>
        simp [handle, RecoveryState.handle, CommitAttemptPacket.tokenValid, sameAttempt, allowed,
          excluded, token, raw, current]

end PhaseRuntimeState

variable [Fintype Player]

/-- Any actual signed input at a clear singleton counted prefix has the same
handling result after projection to the original forced-exit current state. -/
theorem phase_handle_current_sequential_clear_onePacket_history
    (runtime : EventGraphRuntime graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph.sequentialize))
    (plan : RuntimePhasePlan graph.sequentialize)
    (singletons : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    (bounds : MessageBounds graph.sequentialize)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph.sequentialize))
    (present : message ∈ control.execution.network.inputs) :
    (control.execution.application.handle runtime message).map PhaseRuntimeState.current =
      control.execution.application.current.handle runtime
        ⟨message.id, message.payload.packet⟩ := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  have live := (phaseApplication_live runtime leaks).history _ _ _ (fun state supported => by
    obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨PhaseRuntimeState.initial_frontier plan draw, PhaseRuntimeState.initial_live plan draw⟩)
    rawTrace
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler rawTrace
  apply PhaseRuntimeState.handle_current_sequential runtime control.execution.application live.1
    live.2 (phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler rawTrace)
    (phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler rawTrace)
    (phaseAcceptedCheckpointFrame_history runtime leaks plan inputs horizon scheduler rawTrace)
    (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler rawTrace)
    (fun phase member => singletons phase (suffix.subset member)) message
  intro native accepted
  obtain ⟨event, named, ready, _action, _supported⟩ :=
    handle_config_mem_step runtime control.execution.application.current.native native _ accepted
  exact PhaseCount.clear_unfinished_input_attempt runtime leaks plan bounds inputs horizon scheduler
    trace singletons clear message present event named ready.1

end Vegas.EventGraphRuntime
