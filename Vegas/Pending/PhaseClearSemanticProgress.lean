/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSemanticProgress

/-! # Native store preservation when normalization creates no exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- An actually clear physical result cannot take a retry or exhausted-restore
branch. Every automatic phase completion therefore preserves its typed store. -/
theorem settle_keepsStore_of_clear (phases : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph)) (clear : current.excluded = ∅) :
    KeepsStore current.native (settle phases generation entry current retired).current.native := by
  induction phases generalizing generation entry current retired with
  | nil => exact fun _ _ stored => stored
  | cons phase remaining ih =>
    have drainedClear : (phase.drain current).excluded = ∅ :=
      (phase.drain_excluded current).trans clear
    have noFailure : ¬ (phase.kind = .commitment ∧
        (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
      rw [drainedClear]
      simp only [Finset.empty_sdiff, Finset.empty_inter, Finset.not_nonempty_empty,
        and_false, not_false_eq_true]
    by_cases finished : phase.Finished (phase.drain current)
    · rw [settle_clean phase remaining generation entry current retired finished noFailure]
      have next := ih generation (phase.drain current) (phase.drain current) retired drainedClear
      exact fun field value stored => next field value
        (phase.drain_keepsStore current field value stored)
    · simpa only [settle, ite_eq_right finished] using phase.drain_keepsStore current

end PhaseRuntimeState

/-- Crossing a phase boundary without a physical exclusion preserves every
previously written native cell. No equality of endpoint namespaces is required. -/
theorem phaseApplication_clear_semantic_extension (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      after.current.excluded = ∅ → KeepsStore before.current.native after.current.native) where
  refl _ _ := fun _ _ stored => stored
  submit state who material _ := by
    intro field value stored
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).config.store field = some value
    rw [submitStep_config, (material.call.register_facts who state.current.native).1]
    exact stored
  handle state message next accepted clear := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have rawClear : (state.current.inclusionResult message.payload.packet.call native).excluded =
          ∅ := (PhaseRuntimeState.settle_physical _ _ _ _ _).1.symm.trans clear
      have normalized := PhaseRuntimeState.settle_keepsStore_of_clear state.phases state.generation
        state.entry (state.current.inclusionResult message.payload.packet.call native) state.retired
          rawClear
      exact fun field value stored => normalized field value
        (handle_store_of_some runtime _ native _ handled field value stored)
    · cases accepted
  environment state command next reached clear := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      have rawClear : (state.current.environmentResult command native).excluded = ∅ :=
        (PhaseRuntimeState.settle_physical _ _ _ _ _).1.symm.trans clear
      have normalized := PhaseRuntimeState.settle_keepsStore_of_clear state.phases state.generation
        state.entry (state.current.environmentResult command native) state.retired rawClear
      exact fun field value stored => normalized field value
        (environmentStep_store_of_some runtime _ native command supported field value stored)
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact fun _ _ stored => stored

/-- If the actual normalized inclusion is clear, its native handler result
survives normalization, including a clean commitment-phase close. -/
theorem phase_handle_keeps_result_of_clear (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (native : EventGraphRuntime.State graph)
    (handled : EventGraphRuntime.handle runtime state.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native)
    (accepted : state.handle runtime message = some next) (clear : next.current.excluded = ∅) :
    KeepsStore native next.current.native := by
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · rw [handled] at accepted
    cases Option.some.inj accepted
    have rawClear : (state.current.inclusionResult message.payload.packet.call native).excluded =
        ∅ := (PhaseRuntimeState.settle_physical _ _ _ _ _).1.symm.trans clear
    exact PhaseRuntimeState.settle_keepsStore_of_clear state.phases state.generation state.entry
      (state.current.inclusionResult message.payload.packet.call native) state.retired rawClear
  · cases accepted

end Vegas.EventGraphRuntime
