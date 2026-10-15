/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSignedBindings

/-! # Initial binding identities survive every phase restore -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Native input associations are copied by every normalization branch. -/
theorem settle_input_binding (input : graph.InputId) (candidate : Handle graph)
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (saved : entry.native.accepted (.inl input) = some candidate)
    (active : current.native.accepted (.inl input) = some candidate) :
    (settle phases generation entry current retired).entry.native.accepted (.inl input) =
        some candidate ∧
      (settle phases generation entry current retired).current.native.accepted (.inl input) =
        some candidate := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨saved, active⟩
  | cons phase remaining ih =>
      have drained : (phase.drain current).native.accepted (.inl input) = some candidate := by
        rw [(phase.drain_tables current).1]
        exact active
      have rebuilt : (phase.drain (restore entry (phase.drain current))).native.accepted
          (.inl input) = some candidate := by
        rw [(phase.drain_tables _).1]
        exact saved
      simp only [settle]
      split
      · split
        · split
          · exact ⟨saved, rebuilt⟩
          · exact ih _ _ _ _ rebuilt rebuilt
        · exact ih _ _ _ _ drained drained
      · exact ⟨saved, drained⟩

end PhaseRuntimeState

/-- No physical operation changes the distinguished accepted handle of an
initial binding, even when an entire live semantic phase is restored. -/
theorem phaseInputBindingInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (input : graph.InputId) (candidate : Handle graph) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      state.entry.native.accepted (.inl input) = some candidate ∧
        state.current.native.accepted (.inl input) = some candidate) where
  submit state who material valid := by
    refine ⟨valid.1, ?_⟩
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).accepted (.inl input) = some candidate
    rw [submitStep_accepted, Submission.register_accepted]
    exact valid.2
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_input_binding _ _ _ _ _ _ _ valid.1
      change native.accepted (.inl input) = some candidate
      rcases handle_tables_cases runtime state.current.native native _ handled with
        ⟨event, handle, _, _, table, _⟩ | ⟨table, _⟩
      · rw [table, Function.update_of_ne (by simp)]
        exact valid.2
      · rw [table]
        exact valid.2
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_input_binding _ _ _ _ _ _ _ valid.1
      change native.accepted (.inl input) = some candidate
      rw [(environmentStep_tables runtime _ _ command supported).1]
      exact valid.2
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Every actual raw history retains the canonical initial opaque handle. -/
theorem phaseInputBinding_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (input : graph.InputId) (owner : Player) (payload : L.Ty)
    (layout : graph.inputLayout input = .binding owner payload) :
    control.execution.application.current.native.accepted (.inl input) =
      some (owner, .initial input) := by
  have valid := (phaseInputBindingInvariant runtime leaks input (owner, .initial input)).history
    _ horizon scheduler (by
      intro state supported
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.settle_input_binding _ _ _ _ _ _ _
        (State.initial_accepted_binding draw input owner payload layout)
        (State.initial_accepted_binding draw input owner payload layout)) trace
  exact valid.2

end Vegas.EventGraphRuntime
