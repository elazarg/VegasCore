/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnilateralFrontier

/-! # Actual focal source information under public barriers -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- At an actual ready focal event under public barriers, the sampled foreign
frontier and actual physical graph expose exactly the same source observation.
The focal raw policy and foreign private intention values remain unrestricted. -/
theorem ReactiveUnilateralFrontier.normalizeObservation_focal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (event : graph.EventId) (ready : execution.application.config.cut.Ready event)
    (actor : graph.actor? event = some focal) :
    graph.normalizeObservation event focal (graph.playerObserve focal frontier) =
      graph.normalizeObservation event focal
        (graph.playerObserve focal execution.application.config) := by
  have domain : ∀ query, query ∈ frontier.cut.completed ↔
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
  obtain ⟨final, replayed, same⟩ := runtime.unilateralFrontier_foreign_sequence leaks
    ordered.revealRelaxedOrdered profile execution focal memories consistent supported frontier
    related.reachable domain related.settled related.inputs.symm related.recalled
  have originalReady : (runtime.originalConfig leaks execution memories).cut.Ready event := ready
  have observations := (replayed.normalizeObservation_eq ordered event originalReady actor).2
  rw [normalizeObservation_congr_of_semanticKey_eq same event focal, observations,
    runtime.originalConfig_playerObserve_of_empty_memory leaks execution memories
      focal related.empty]

end Vegas.EventGraphRuntime
