/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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
  revert saved active
  fun_induction settle with
  | case1 => exact fun saved active => ⟨saved, active⟩
  | case2 phase _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro saved _active
      refine ⟨saved, ?_⟩
      rwa [(phase.drain_tables _).1]
  | case3 phase _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro saved _active
      apply ih <;> rwa [(phase.drain_tables _).1]
  | case4 phase _ _ _ _ _ _ _ _ ih =>
      intro _saved active
      apply ih <;> rwa [(phase.drain_tables _).1]
  | case5 phase _ _ _ _ _ _ _ =>
      intro saved active
      refine ⟨saved, ?_⟩
      rwa [(phase.drain_tables _).1]

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
