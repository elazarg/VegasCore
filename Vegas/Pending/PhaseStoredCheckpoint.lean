/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingInvariant

/-! # Saved semantic values throughout physical attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RuntimePhase

/-- Automatic current-phase service never rewrites a checkpoint cell. -/
theorem drainFuel_keepsStore (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) :
    KeepsStore state.native (phase.drainFuel fuel state).native := by
  apply phase.drainFuel_induction (fun next => KeepsStore state.native next.native)
    (fun before event eligible previous => ?_) fuel state (fun _ _ stored => stored)
  obtain ⟨action, supported⟩ := before.completeAutomatic_step event eligible.2
  exact fun field value stored => before.native.config.step_store_of_some
    _ _ _ action supported field value (previous field value stored)

theorem drain_keepsStore (phase : RuntimePhase graph) (state : RecoveryState graph) :
    KeepsStore state.native (phase.drain state).native :=
  phase.drainFuel_keepsStore _ _

end RuntimePhase

namespace PhaseRuntimeState

/-- Live execution extends the semantic checkpoint; a retry restores that
checkpoint before automatic service resumes. -/
def StoredCheckpoint (state : PhaseRuntimeState graph) : Prop :=
  KeepsStore state.entry.native state.current.native

/-- Every automatic phase advance and retry retains its newly selected checkpoint. -/
theorem settle_storedCheckpoint (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (stored : KeepsStore entry.native current.native) :
    (settle phases generation entry current retired).StoredCheckpoint := by
  induction phases generalizing generation entry current retired with
  | nil => exact stored
  | cons phase remaining ih =>
      have drained : KeepsStore entry.native (phase.drain current).native :=
        fun field value present => phase.drain_keepsStore current field value
          (stored field value present)
      simp only [settle]
      split
      · split
        · split
          · exact phase.drain_keepsStore _
          · exact ih _ _ _ _ (fun _ _ present => present)
        · exact ih _ _ _ _ (fun _ _ present => present)
      · exact drained

theorem initial_storedCheckpoint (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).StoredCheckpoint :=
  settle_storedCheckpoint _ _ _ _ _ (fun _ _ present => present)

end PhaseRuntimeState

/-- Primitive physical operations retain all semantic cells saved before the phase. -/
theorem phaseApplication_storedCheckpoint (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.StoredCheckpoint where
  submit state who material valid := by
    intro field value stored
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).config.store field = some value
    rw [submitStep_config, (material.call.register_facts who state.current.native).1]
    exact valid field value stored
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_storedCheckpoint
      intro field value present
      exact handle_store_of_some runtime _ native _ handled field value (valid field value present)
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_storedCheckpoint
      intro field value present
      exact environmentStep_store_of_some runtime _ native command supported field value
        (valid field value present)
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Every actual initialized history preserves its currently saved semantic values. -/
theorem phaseStoredCheckpoint_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.StoredCheckpoint :=
  (phaseApplication_storedCheckpoint runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_storedCheckpoint plan draw) trace

end Vegas.EventGraphRuntime
