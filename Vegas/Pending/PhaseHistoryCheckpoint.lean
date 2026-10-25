/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseStoredCheckpoint

/-! # Surviving chronological histories extend their saved checkpoint -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RuntimePhase

/-- Automatic completions append their original dependent actions. -/
theorem drainFuel_history_prefix (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) :
    state.native.config.history.IsPrefix (phase.drainFuel fuel state).native.config.history := by
  apply phase.drainFuel_induction
    (fun next => state.native.config.history.IsPrefix next.native.config.history)
    (fun before event eligible previous => ?_) fuel state ⟨[], by simp⟩
  obtain ⟨action, supported⟩ := before.completeAutomatic_step event eligible.2
  apply previous.trans
  rw [before.native.config.step_history event eligible.2.1 action _ supported]
  exact ⟨_, rfl⟩

theorem drain_history_prefix (phase : RuntimePhase graph) (state : RecoveryState graph) :
    state.native.config.history.IsPrefix (phase.drain state).native.config.history :=
  phase.drainFuel_history_prefix _ _

end RuntimePhase

namespace PhaseRuntimeState

/-- A retry discards only the live suffix of effective semantic actions. -/
def HistoryCheckpoint (state : PhaseRuntimeState graph) : Prop :=
  state.entry.native.config.history.IsPrefix state.current.native.config.history

theorem settle_historyCheckpoint (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (history : entry.native.config.history.IsPrefix current.native.config.history) :
    (settle phases generation entry current retired).HistoryCheckpoint := by
  revert history
  fun_induction settle with
  | case1 => exact id
  | case2 phase _ _ _ _ _ _ _ _ _ _ _ _ => exact fun _ => phase.drain_history_prefix _
  | case3 _ _ _ _ _ _ _ _ _ _ _ _ _ ih | case4 _ _ _ _ _ _ _ _ _ ih =>
      exact fun _ => ih (⟨[], by simp⟩)
  | case5 phase _ _ _ current _ _ _ =>
      exact fun history => history.trans (phase.drain_history_prefix current)

theorem initial_historyCheckpoint (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).HistoryCheckpoint :=
  settle_historyCheckpoint _ _ _ _ _ (⟨[], by simp⟩)

end PhaseRuntimeState

/-- Every physical primitive retains saved dependent completion actions. -/
theorem phaseApplication_historyCheckpoint (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.HistoryCheckpoint where
  submit state who material valid := by
    change state.entry.native.config.history.IsPrefix
      (submitStep (material.call.register state.current.native who) who
        material.call.packet).config.history
    rw [submitStep_config, (material.call.register_facts who state.current.native).1]
    exact valid
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_historyCheckpoint
      obtain ⟨event, _named, ready, action, supported⟩ :=
        handle_config_mem_step runtime _ native _ handled
      apply valid.trans
      change state.current.native.config.history.IsPrefix native.config.history
      rw [state.current.native.config.step_history _ _ _ _ supported]
      exact ⟨_, rfl⟩
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      apply PhaseRuntimeState.settle_historyCheckpoint
      exact valid.trans (environmentStep_history_prefix runtime _ native command supported)
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid

/-- The complete actual history derives chronological checkpoint retention. -/
theorem phaseHistoryCheckpoint_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.HistoryCheckpoint :=
  (phaseApplication_historyCheckpoint runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_historyCheckpoint plan draw) trace

end Vegas.EventGraphRuntime
