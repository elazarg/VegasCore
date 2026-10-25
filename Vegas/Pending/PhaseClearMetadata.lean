/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication

/-! # Clear executions have no retired attempts or retry generation

An archive is installed only at a fresh permanent exclusion. This is a property
of the actual phase engine, independent of payoffs, policies and phase widths.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Without an excluded owner, settlement neither retires an attempt nor retries. -/
theorem settle_clear_metadata (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (clear : current.excluded = ∅) :
    (settle phases generation entry current retired).generation = generation ∧
      (settle phases generation entry current retired).retired = retired := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨rfl, rfl⟩
  | cons phase remaining ih =>
      have drainedClear : (phase.drain current).excluded = ∅ :=
        (phase.drain_excluded current).trans clear
      have noFailure : ¬ (phase.kind = .commitment ∧
          (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
        rw [drainedClear, Finset.empty_sdiff, Finset.empty_inter]
        simp
      simp only [settle, ite_eq_right noFailure]
      split
      · exact ih generation (phase.drain current) (phase.drain current) retired drainedClear
      · exact ⟨rfl, rfl⟩

/-- Initialization has no retirement and generation zero for every actual plan. -/
theorem initial_clear_metadata (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).generation = 0 ∧ (initial plan inputs).retired = [] :=
  settle_clear_metadata _ _ _ _ _ rfl

end Vegas.EventGraphRuntime.PhaseRuntimeState

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every raw operation retains empty metadata as long as no permanent
exclusion has occurred. This includes arbitrary scheduling and player responses. -/
theorem phaseApplication_clear_metadata (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state => state.current.excluded = ∅ →
      state.generation = 0 ∧ state.retired = []) where
  submit _state _who _submission valid := valid
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      intro clear
      change (PhaseRuntimeState.settle _ _ _ _ _).current.excluded = ∅ at clear
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1] at clear
      have earlier : state.current.excluded = ∅ :=
        Finset.subset_empty.mp (clear ▸ state.current.inclusionResult_excluded_subset _ native)
      obtain ⟨generation, retired⟩ :=
        PhaseRuntimeState.settle_clear_metadata state.phases state.generation state.entry
          (state.current.inclusionResult message.payload.packet.call native) state.retired clear
      exact ⟨generation.trans (valid earlier).1, retired.trans (valid earlier).2⟩
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, _supported, rfl⟩ := reached
      intro clear
      change (PhaseRuntimeState.settle _ _ _ _ _).current.excluded = ∅ at clear
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1] at clear
      have earlier : state.current.excluded = ∅ :=
        Finset.subset_empty.mp
          (clear ▸ state.current.environmentResult_excluded_subset command native)
      obtain ⟨generation, retired⟩ :=
        PhaseRuntimeState.settle_clear_metadata state.phases state.generation state.entry
          (state.current.environmentResult command native) state.retired clear
      exact ⟨generation.trans (valid earlier).1, retired.trans (valid earlier).2⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Actual initialized clear histories expose neither retired snapshots nor
a retry-generation tag. No equilibrium-path or singleton-phase premise is used. -/
theorem phaseClearMetadata_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    control.execution.application.generation = 0 ∧ control.execution.application.retired = [] :=
  (phaseApplication_clear_metadata runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact fun _ => PhaseRuntimeState.initial_clear_metadata plan draw) trace clear

/-- Every nonempty actual archive certifies a public permanent exclusion. -/
theorem phaseRetired_excluded_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (retired : control.execution.application.retired ≠ []) :
    control.execution.application.current.excluded ≠ ∅ := by
  intro clear
  exact retired
    (phaseClearMetadata_history runtime leaks plan inputs horizon scheduler trace clear).2

end Vegas.EventGraphRuntime
