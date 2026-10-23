/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowRefinement

/-! # Successful-store refinement through actual native progress

An old shadow is supported on completed events. Any new ready event is
therefore outside that shadow, regardless of its actual evaluator outcome.
The owning CompletionStep evidence supplies the real configuration step.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Existing completed private overrides survive one actual native progress
step. A new binding's result is unchanged here; bad-only accepting repairs
have their own separate event-indexed preparation argument. -/
theorem CompletedAt.completionStep_refinement {memory : BindingShadow graph}
    {state next : State graph} (supported : memory.CompletedAt state.config) (owner : Player)
    (preserved : (memory.native owner state).config.store.BindingRefines state.config.store)
    (progressed : CompletionStep state next) :
    (memory.native owner next).config.store.BindingRefines next.config.store := by
  rcases progressed with unchanged | ⟨event, ready, action, reached, _times, _accepted⟩
  · change (memory.config next.config).store.BindingRefines next.config.store
    rw [unchanged.1]
    exact preserved
  · rw [Config.step] at reached
    obtain ⟨value, _drawn, completeEq⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
    have empty := supported.ready_none event ready
    have completed : Store.BindingRefines
        (memory.config (state.config.complete event ready action value)).store
        (state.config.complete event ready action value).store := by
      rw [config_complete_unmodified memory state.config event ready empty.2 empty.1 action value]
      exact Config.bindingRefines_complete preserved event ready ready action action value value
        (EventField.BindingRefines.refl _ _)
    change (memory.config next.config).store.BindingRefines next.config.store
    rw [← completeEq]
    exact completed

/-- Every actual environment command has the required owning progress
witness. No additional law, chance independence, or read-cone premise is used. -/
theorem CompletedAt.environment_refinement {memory : BindingShadow graph}
    {state next : State graph} (supported : memory.CompletedAt state.config) (owner : Player)
    (preserved : (memory.native owner state).config.store.BindingRefines state.config.store)
    (runtime : EventGraphRuntime graph) (command : EnvironmentCommand graph)
    (reached : next ∈ (environmentStep runtime state command).support) :
    (memory.native owner next).config.store.BindingRefines next.config.store :=
  supported.completionStep_refinement owner preserved
    (completionStep_environmentStep runtime state next command reached)

end Vegas.EventGraphRuntime.BindingShadow
