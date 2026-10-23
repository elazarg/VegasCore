/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseResolution

/-! # Literal control records inside one physical phase namespace -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every real operation preserving its physical namespace retains the
installed descriptors and literal retired-attempt archive. -/
theorem phaseApplication_sameAttempt_controls (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after => before.Ordered →
      before.attempt = after.attempt →
        after.phases = before.phases ∧ after.retired = before.retired) where
  refl _ _ _ := ⟨rfl, rfl⟩
  submit _ _ _ _ _ := ⟨rfl, rfl⟩
  handle state message next accepted ordered same := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have settled := PhaseRuntimeState.settle_of_same_namespace
        state.phases state.generation state.entry
        (state.current.inclusionResult message.payload.packet.call native) state.retired ordered
          same
      have phases := congrArg PhaseRuntimeState.phases settled
      have retired := congrArg PhaseRuntimeState.retired settled
      exact ⟨phases, retired⟩
    · cases accepted
  environment state command next reached ordered same := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      have settled := PhaseRuntimeState.settle_of_same_namespace
        state.phases state.generation state.entry (state.current.environmentResult command native)
        state.retired ordered same
      have phases := congrArg PhaseRuntimeState.phases settled
      have retired := congrArg PhaseRuntimeState.retired settled
      exact ⟨phases, retired⟩
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, rfl⟩

end Vegas.EventGraphRuntime
