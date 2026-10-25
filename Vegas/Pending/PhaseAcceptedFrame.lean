/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseFrontier
import Vegas.Pending.PhaseResolution
import Vegas.Pending.ReactiveSignedCommitments

/-! # Exact accepted-table frames at actual phase checkpoints

Any association differing from the saved checkpoint belongs to an event already
completed inside the current phase. This is a factual raw-runtime invariant;
unusable accepted commitments and arbitrary later responses are included.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Every changed association was installed by a completed current-phase event. -/
def AcceptedCheckpointFrame (state : PhaseRuntimeState graph) : Prop :=
  ∀ field, state.current.native.accepted field ≠ state.entry.native.accepted field →
    ∃ phase ∈ state.phases.head?, ∃ event ∈ phase.events,
      field = .inr event ∧ event ∈ state.current.native.config.cut.completed

theorem settle_acceptedCheckpointFrame (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (frame : AcceptedCheckpointFrame ⟨phases, generation, entry, current, retired⟩) :
    (settle phases generation entry current retired).AcceptedCheckpointFrame := by
  revert frame
  fun_induction settle with
  | case1 => exact id
  | case2 phase remaining generation entry current retired drained finished failed
      checkpoint rebuilt archive survivors =>
      intro _ field changed
      have unchanged :
          (phase.drain (restore entry (phase.drain current))).native.accepted field =
            entry.native.accepted field := by
        rw [(phase.drain_tables _).1]
        rfl
      exact (changed unchanged).elim
  | case3 phase remaining generation entry current retired drained finished failed
      checkpoint rebuilt archive exhausted ih =>
      exact fun _ => ih (fun _ changed => (changed rfl).elim)
  | case4 phase remaining generation entry current retired drained finished clean ih =>
      exact fun _ => ih (fun _ changed => (changed rfl).elim)
  | case5 phase remaining generation entry current retired drained unfinished =>
      intro frame field changed
      have oldChanged : current.native.accepted field ≠ entry.native.accepted field := by
        intro same
        apply changed
        change (phase.drain current).native.accepted field = entry.native.accepted field
        rw [(phase.drain_tables current).1]
        exact same
      obtain ⟨target, head, event, inside, named, completed⟩ := frame field oldChanged
      exact ⟨target, head, event, inside, named, phase.drain_completed current completed⟩

theorem initial_acceptedCheckpointFrame (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).AcceptedCheckpointFrame :=
  settle_acceptedCheckpointFrame _ _ _ _ _ (fun _ changed => (changed rfl).elim)

omit [DecidableEq Player] in
theorem AcceptedCheckpointFrame.copy_current {state : PhaseRuntimeState graph}
    (frame : state.AcceptedCheckpointFrame) (next : RecoveryState graph)
    (accepted : next.native.accepted = state.current.native.accepted)
    (completed : state.current.native.config.cut.completed ⊆ next.native.config.cut.completed) :
    AcceptedCheckpointFrame { state with current := next } := by
  intro field changed
  obtain ⟨phase, head, event, inside, named, done⟩ :=
    frame field (by simpa only [accepted] using changed)
  exact ⟨phase, head, event, inside, named, completed done⟩

omit [DecidableEq Player] in
/-- The association frame identifies the exact saved table before an unfinished
singleton event, without restricting the values or number of authored responses. -/
theorem AcceptedCheckpointFrame.eq_of_singleton {state : PhaseRuntimeState graph}
    (frame : state.AcceptedCheckpointFrame) (phase : RuntimePhase graph)
    (head : state.phases.head? = some phase) (event : graph.EventId)
    (only : phase.events = {event})
    (unfinished : event ∉ state.current.native.config.cut.completed) :
    state.current.native.accepted = state.entry.native.accepted := by
  classical
  funext field
  by_contra changed
  obtain ⟨target, member, completedEvent, inside, _, done⟩ := frame field changed
  have same : target = phase :=
    (show phase = target by simpa only [head, Option.mem_some_iff] using member).symm
  subst target
  have equal := Finset.mem_singleton.mp ((Finset.ext_iff.mp only _).mp inside)
  subst completedEvent
  exact unfinished done

end PhaseRuntimeState

/-- Every actual primitive preserves the exact phase association footprint. -/
theorem phaseApplication_acceptedCheckpointFrame (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.AcceptedCheckpointFrame where
  submit state who submission frame := by
    apply frame.copy_current
    · change (submitStep (submission.call.register state.current.native who) who
        submission.call.packet).accepted = state.current.native.accepted
      rw [submitStep_accepted, Submission.register_accepted]
    · change state.current.native.config.cut.completed ⊆
        (submitStep (submission.call.register state.current.native who) who
          submission.call.packet).config.cut.completed
      rw [submitStep_config, (submission.call.register_facts who state.current.native).1]
  handle state message next frame accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_acceptedCheckpointFrame
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      obtain ⟨phase, head, event, named, inside⟩ :=
        PhaseRuntimeState.allows_event state _ authorized
      obtain ⟨actual, actualNamed, ready, action, supported⟩ :=
        handle_config_mem_step runtime state.current.native native _ rawAccepted
      have same : actual = event := Option.some.inj (actualNamed.symm.trans named)
      subst actual
      have kept := State.completed_subset_of_mem_step _ _ ready action _ supported
      rcases handle_tables_cases runtime state.current.native native _ rawAccepted with
        ⟨binding, candidate, call, _candidates, table, _owner⟩ | ⟨table, _candidates⟩
      · have bindingEq : binding = event := by
          change message.payload.packet.call = .commitment binding candidate at call
          rw [call] at named
          exact Option.some.inj named
        subst binding
        intro field changed
        change native.accepted field ≠ state.entry.native.accepted field at changed
        by_cases current : field = .inr event
        · refine ⟨phase, head, event, inside, current, ?_⟩
          change event ∈ native.config.cut.completed
          rw [state.current.native.config.step_cut event ready action _ supported]
          simp
        · have sameTable : native.accepted field = state.current.native.accepted field := by
            rw [table, Function.update_of_ne current]
          obtain ⟨previous, previousHead, old, oldInside, oldNamed, done⟩ :=
            frame field (fun equal => changed (sameTable.trans equal))
          exact ⟨previous, previousHead, old, oldInside, oldNamed, kept done⟩
      · exact frame.copy_current _ table kept
    · cases accepted
  environment state command next frame reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_acceptedCheckpointFrame
      exact frame.copy_current _ (environmentStep_tables runtime _ native command supported).1
        (environmentStep_completed_subset runtime _ native command supported)
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact frame

/-- Initialized actual histories supply the frame against every raw response policy. -/
theorem phaseAcceptedCheckpointFrame_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.AcceptedCheckpointFrame :=
  (phaseApplication_acceptedCheckpointFrame runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_acceptedCheckpointFrame plan draw) trace

end Vegas.EventGraphRuntime
