/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionApplication

/-! # Native kernels classified at the first exclusion

Before exclusion the classifier retains the complete native state. At and after
exclusion it retains the permanent excluded set. Automatic completion preserves
this classifier, so the ordinary native inclusion and environment kernels give
exact classified recovery kernels without exposing post-exclusion states.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryState

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Retain the native state before exclusion and the permanent excluded set
once exclusion has occurred. -/
def exclusionBoundary (state : RecoveryState graph) : State graph ⊕ Finset Player :=
  if state.excluded = ∅ then Sum.inl state.native else Sum.inr state.excluded

/-- Automatic failure completion preserves the boundary classifier. -/
theorem exclusionBoundary_drain (state : RecoveryState graph) :
    state.drain.exclusionBoundary = state.exclusionBoundary := by
  classical
  by_cases empty : state.excluded = ∅
  · rw [drain_eq_of_empty state empty]
  · simp only [exclusionBoundary, drain_excluded, empty, ↓reduceIte]

/-- From a clear excluded set, classified packet handling is the ordinary
native handler followed by the inclusion classifier. Rejected packets remain
rejected, and the crossing records the newly excluded owner. -/
theorem handle_exclusionBoundary_of_empty (runtime : EventGraphRuntime graph)
    (state : RecoveryState graph) (message : Message Player (WitnessedPacket graph))
    (empty : state.excluded = ∅) :
    (state.handle runtime message).map exclusionBoundary =
      if message.payload.tokenValid then
        (EventGraphRuntime.handle runtime state.native ⟨message.id, message.payload.call⟩).map
          (fun native => (state.inclusionResult message.payload.call native).exclusionBoundary)
      else none := by
  classical
  unfold handle
  rw [excludedCall_of_empty state empty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs
  · simp only [Option.map_map, Function.comp_def, exclusionBoundary_drain]
  · rfl

/-- Classified environment evolution is exactly the ordinary native kernel
followed by the expiry classifier, including the first exclusion transition. -/
theorem environment_exclusionBoundary (runtime : EventGraphRuntime graph)
    (state : RecoveryState graph) (command : EnvironmentCommand graph) :
    (state.environment runtime command).map exclusionBoundary =
      (environmentStep runtime state.native command).map
        (fun native => (state.environmentResult command native).exclusionBoundary) := by
  classical
  simp only [environment, PMF.map_comp, Function.comp_def, exclusionBoundary_drain]

end Vegas.EventGraphRuntime.RecoveryState
