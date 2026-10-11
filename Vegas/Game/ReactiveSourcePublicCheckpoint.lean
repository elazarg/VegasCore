/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnilateralObservation
import Vegas.Compile.EventGraphPolicyBacktranslation

/-! # Actual public source checkpoints with one arbitrary raw player -/

noncomputable section
namespace Vegas
open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A ready public focal decision exposes a constructively decoded chronological
source view, even when its raw policy is arbitrary and foreign intentions are
sampled ahead of physical settlement. No source/noise law is assumed. -/
theorem encodeDecisionView?_unilateral_public_checkpoint
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (refsBefore : ContextRefsBefore refs embedding)
    (index : Fin (eventCount program))
    (covered : refs.CoversPrefix whole (embedding.event index).val)
    (profile : (toEventGraph whole).BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (memories : Player → List (Option (toEventGraph whole).Completion))
    (frontier : (toEventGraph whole).Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (ready : execution.application.config.cut.Ready (embedding.event index))
    (actor : (toEventGraph whole).actor? (embedding.event index) = some focal)
    (isPublic : ((toEventGraph whole).outputLayout (embedding.event index)).IsPublic) :
    ∃ observation,
      decodeObservation? focal refs ((toEventGraph whole).playerStore focal frontier.store) =
        some observation ∧
      encodeDecisionView? whole refs focal (embedding.event index)
        (observation, decodeCompletions whole
          ((toEventGraph whole).ownCompletions focal execution.application.config.history)) =
        some ((toEventGraph whole).normalizeObservation (embedding.event index) focal
          ((toEventGraph whole).playerObserve focal execution.application.config)) := by
  let graph := toEventGraph whole
  have domain : ∀ query, query ∈ frontier.cut.completed ↔
      query ∈ execution.application.config.cut.completed ∨
        ∃ owner, owner ≠ focal ∧ ∃ remembered,
          some remembered ∈ memories owner ∧ remembered.event = query := by
    intro query
    rw [related.domain query]
    constructor
    · rintro (physical | ⟨owner, remembered, member, named⟩)
      · exact Or.inl physical
      · exact Or.inr ⟨owner, related.retained_foreign runtime leaks focal execution
          memories frontier owner ⟨remembered, member⟩, remembered, member, named⟩
    · rintro (physical | ⟨owner, _, remembered, member, named⟩)
      · exact Or.inl physical
      · exact Or.inr ⟨owner, remembered, member, named⟩
  have ghostReady := runtime.unilateralFrontier_ready leaks profile execution focal memories
    consistent supported frontier domain (embedding.event index) actor ready
  have chronological : frontier.cut.IsPrefix (embedding.event index).val := by
    refine ⟨Nat.le_of_lt (embedding.event index).isLt, ?_⟩
    intro other
    exact EventGraph.barrierOrder_ready_public_completed_iff (outputLayout whole)
      frontier.cut ghostReady isPublic other
  obtain ⟨observation, decoded⟩ := exists_decodeObservation_of_prefix whole refs embedding
    refsBefore index (embedding.event index).val frontier chronological rfl focal
  refine ⟨observation, decoded, ?_⟩
  have encoded := encodeDecisionView?_decodeActual_eq_normalizeObservation whole refs
    (embedding.event index).val covered execution.application.config.inputs frontier
    related.reachable chronological (embedding.event index) ghostReady focal actor
    observation decoded
  have own : graph.ownCompletions focal frontier.history =
      graph.ownCompletions focal execution.application.config.history := by
    simpa using related.intentions focal
  rw [own] at encoded
  rw [encoded]
  exact congrArg some (related.normalizeObservation_focal runtime leaks
    (toEventGraph_barrierOrdered whole) profile execution focal memories frontier
    consistent supported (embedding.event index) ready actor)

end Vegas
