/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnilateralEnvironment

/-! # Actual focal expiry in a mixed source frontier -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Native expiry at a focal event admits a coupled reachable source frontier,
without prescribing the focal player's raw responses. -/
theorem ReactiveUnilateralFrontier.expire_focal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution after : (runtime.reactiveApplication leaks).Execution)
    (focal : Player) (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supportedMemory : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (supported : after ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support) :
    ∃ final, runtime.ReactiveUnilateralFrontier leaks focal after memories final := by
  unfold ReactiveApplication.Execution.environmentStep at supported
  obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ moved
  change state ∈ (runtime.environmentStep execution.application (.expire event)).support at changed
  rcases environmentStep_expire_config_eq_or_mem_step runtime execution.application state event
      changed with unchanged | ⟨physicalReady, action, physical⟩
  · refine ⟨frontier, ?_⟩
    exact related.congr_execution runtime leaks execution _ focal memories frontier
      unchanged.symm rfl rfl
  · have domain : ∀ query, query ∈ frontier.cut.completed ↔
        query ∈ execution.application.config.cut.completed ∨
          ∃ owner, owner ≠ focal ∧ ∃ remembered,
            some remembered ∈ memories owner ∧ remembered.event = query := by
      intro query
      rw [related.domain query]
      constructor
      · rintro (physical | ⟨owner, remembered, member, named⟩)
        · exact Or.inl physical
        · refine Or.inr ⟨owner, ?_, remembered, member, named⟩
          intro same
          subst owner
          simp [related.empty] at member
      · rintro (physical | ⟨owner, _, remembered, member, named⟩)
        · exact Or.inl physical
        · exact Or.inr ⟨owner, remembered, member, named⟩
    obtain ⟨frontierReady, joint, first, second, common⟩ :=
      runtime.unilateralFrontier_coupled_step leaks profile execution focal memories
        consistent supportedMemory frontier domain related.settled related.inputs.symm event actor
          physicalReady action
    have afterSupport : state.config ∈ (joint.map Prod.fst).support := by
      rw [first]
      exact physical
    obtain ⟨pair, pairSupported, pairFirst⟩ := PMF.support_map .. ▸ afterSupport
    have finalSupported : pair.2 ∈ (frontier.step event frontierReady action).support := by
      rw [← second, PMF.support_map]
      exact ⟨pair, pairSupported, rfl⟩
    obtain ⟨settled, sameInputs⟩ := common pair pairSupported
    refine ⟨pair.2, ?_⟩
    apply ReactiveUnilateralFrontier.step_focal runtime leaks focal execution _
      memories frontier pair.2 related event actor physicalReady frontierReady action
    · exact physical
    · exact finalSupported
    · change state.config.CompletedOutputAgreement pair.2
      rw [← pairFirst]
      exact settled
    · change state.config.inputs = pair.2.inputs
      rw [← pairFirst]
      exact sameInputs
    · change state.config.history.map (runtime.originalCompletion leaks _ memories) = _
      rw [execution.application.config.step_history event physicalReady action
        state.config physical]
      simp only [List.map_append, List.map_singleton]
      change execution.application.config.history.map
          (runtime.originalCompletion leaks { execution with application := state } memories) ++
        [runtime.originalCompletion leaks { execution with application := state } memories
          ⟨event, action⟩] = _
      have originals : runtime.originalCompletion leaks
          { execution with application := state } memories =
          runtime.originalCompletion leaks execution memories := rfl
      rw [originals]
      have current : runtime.originalCompletion leaks execution memories ⟨event, action⟩ =
          ⟨event, action⟩ := by
        simp only [originalCompletion, actor, related.empty]
        cases node : nodeView graph event <;> simp [reactiveOriginal, node]
      rw [current]
      rfl

end Vegas.EventGraphRuntime
