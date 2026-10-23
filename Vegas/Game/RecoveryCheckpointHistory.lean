/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySourceEnvironment

/-! # Actual initialized phased histories have reachable typed source checkpoints -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem phase_source_invariant
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      Nonempty (RecoverySourceWitness setup mode plan state)) where
  submit state owner material valid := by
    obtain ⟨witness⟩ := valid
    exact ⟨witness.submit runtime leaks owner material⟩
  handle state message next valid accepted := by
    obtain ⟨witness⟩ := valid
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨result, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      obtain ⟨nextWitness, _delta, _fuel, _sourcePath⟩ :=
        witness.after_handle runtime leaks maximal message result
        allowed handled
      exact ⟨nextWitness⟩
    · cases accepted
  environment state command next valid reached := by
    obtain ⟨witness⟩ := valid
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i authorized
      obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      obtain ⟨nextWitness, _delta, _fuel, _sourcePath⟩ :=
        witness.after_environment_source runtime leaks maximal command result
        authorized supported
      exact ⟨nextWitness⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact ⟨witness⟩

/-- Every actual initialized phased history has a saved typed source
checkpoint reached in the actual auxiliary recovery protocol. This includes
arbitrary legal player behavior, native schedules and every reset. No source
path, source outcome, exclusion agreement or simulation witness is assumed. -/
theorem recoverySourceCheckpoint_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control)) :
    ∃ checkpoint : RecoverySourceCheckpoint setup mode control.execution.application,
      checkpoint.ArchivedRecall ∧ checkpoint.PublicChronology plan ∧
      ArchivedSourceOrigins setup mode control.execution.application.retired
        ⟨_, checkpoint.trace⟩ := by
  have invariant := phase_source_invariant setup mode runtime leaks plan maximal
  have valid := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · obtain ⟨witness⟩ := valid
    exact ⟨witness.checkpoint, witness.aligned, witness.chronology, witness.origins⟩
  · obtain ⟨draw, drawSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨RecoverySourceWitness.initialized setup mode plan draw drawSupport⟩

end Vegas
