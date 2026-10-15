/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearNativeProgress

/-! # Clear phase advances retain every unfinished active event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- A clear normalization cannot leave the head interval while one of its
events is unfinished. This uses the actual finished test, not graph readiness. -/
theorem normalize_phases_of_unfinished (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : state.phases = phase :: remaining) (event : graph.EventId)
    (inside : event ∈ phase.events) (clear : state.normalize.current.excluded = ∅)
    (unfinished : event ∉ state.normalize.current.native.config.cut.completed) :
    state.normalize.phases = state.phases := by
  classical
  have currentEq := (normalize_of_clear state clear).1
  have originalClear := (congrArg RecoveryState.excluded currentEq).symm.trans clear
  have drained := phase.drain_eq_of_clear state.current (by
    rintro query ⟨_, automatic⟩
    obtain ⟨owner, _, excluded⟩ := automatic.owned
    simp only [originalClear, Finset.notMem_empty] at excluded)
  have notFinished : ¬ phase.Finished (phase.drain state.current) := by
    intro finished
    apply unfinished
    rw [currentEq, ← drained]
    exact finished inside
  unfold normalize
  rw [installed]
  simp only [settle, notFinished, ↓reduceIte]

end PhaseRuntimeState

/-- Arbitrary genuine phase operations preserve the installed interval if an
event in that interval survives unfinished at a clear endpoint. -/
theorem phaseApplication_clear_phasePersistence (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      after.current.excluded = ∅ → ∀ phase remaining,
        before.phases = phase :: remaining → ∀ event, event ∈ phase.events →
          event ∉ after.current.native.config.cut.completed → after.phases = before.phases) where
  refl _ _ _ _ _ _ _ _ := rfl
  submit _ _ _ _ _ _ _ _ _ _ := rfl
  handle state message next accepted clear phase remaining installed event inside unfinished := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.normalize_phases_of_unfinished _ phase remaining installed
        event inside clear unfinished
    · cases accepted
  environment state command next reached clear phase remaining installed event inside
      unfinished := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _, rfl⟩ := PMF.support_map .. ▸ reached
      exact PhaseRuntimeState.normalize_phases_of_unfinished _ phase remaining installed
        event inside clear unfinished
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl

end Vegas.EventGraphRuntime
