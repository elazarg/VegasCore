/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionNativeFailure

/-! # Public failure records when no compiled event completes -/

noncomputable section

namespace Vegas.EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Accepted handles cannot change along a completion step that leaves the
compiled configuration unchanged. -/
theorem CompletionStep.accepted_eq_of_config_eq {before after : State graph}
    (step : CompletionStep before after) (same : after.config = before.config) :
    after.accepted = before.accepted := by
  rcases step with ⟨_config, accepted, _activated⟩ |
    ⟨event, ready, action, supported, _activated, _accepted⟩
  · exact accepted
  · have completed : event ∈ after.config.cut.completed := by
      rw [before.config.step_cut event ready action _ supported, EventOrder.Cut.mem_complete]
      exact Or.inl rfl
    rw [same] at completed
    exact (ready.1 completed).elim

omit [DecidableEq Player] in
/-- Every native completion step preserves all previously completed events. -/
theorem CompletionStep.completed_mono {before after : State graph}
    (step : CompletionStep before after) :
    before.config.cut.completed ⊆ after.config.cut.completed := by
  rcases step with ⟨same, _accepted, _activated⟩ |
    ⟨event, ready, action, supported, _activated, _accepted⟩
  · rw [same]
  · intro query completed
    rw [before.config.step_cut event ready action _ supported, EventOrder.Cut.mem_complete]
    exact Or.inr completed

omit [DecidableEq Player] in
/-- With no change to the compiled configuration, an actual native operation
retains exactly the same public exclusion record. -/
theorem PublicExclusionRecord.completionStep_sameConfig
    {before after : State graph} {excluded : Finset Player}
    (valid : PublicExclusionRecord (RecoveryState.mk before excluded))
    (step : CompletionStep before after) (same : after.config = before.config) :
    PublicExclusionRecord (RecoveryState.mk after excluded) := by
  have accepted := step.accepted_eq_of_config_eq same
  refine ⟨valid.receipts.step step, fun owner => ?_⟩
  rw [valid.excluded owner]
  constructor
  · rintro ⟨event, acting, failed⟩
    exact ⟨event, acting, (State.PublicFailure.congr event (by rw [same])
      (by rw [same]) (congrFun accepted (.inr event))).mpr failed⟩
  · rintro ⟨event, acting, failed⟩
    exact ⟨event, acting, (State.PublicFailure.congr event (by rw [same])
      (by rw [same]) (congrFun accepted (.inr event))).mp failed⟩

end Vegas.EventGraphRuntime
