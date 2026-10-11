/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOriginalConfig
import Vegas.EventGraph.CompletedOutputAgreement

/-! # Reachable retained frontiers on the actual source configuration -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Structural coupling between one actual physical execution and a reachable
configuration retaining sampled decisions ahead of their physical settlement. -/
structure ReactiveRetainedFrontier (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config) : Prop where
  reachable : frontier.Reachable execution.application.config.inputs
  inputs : frontier.inputs = execution.application.config.inputs
  domain : ∀ event, event ∈ frontier.cut.completed ↔
    event ∈ execution.application.config.cut.completed ∨
      ∃ owner remembered, some remembered ∈ memories owner ∧ remembered.event = event
  settled : execution.application.config.CompletedOutputAgreement frontier
  recalled : ∀ owner, graph.ownCompletions owner
    (runtime.originalConfig leaks execution memories).history <+:
      graph.ownCompletions owner frontier.history

theorem updatedIntentionEvents
    (memories : Player → List (Option graph.Completion)) (who : Player)
    (saved : Option graph.Completion) (query : graph.EventId) :
    (∃ owner remembered, some remembered ∈
        Function.update memories who (memories who ++ [saved]) owner ∧ remembered.event = query) ↔
      (∃ owner remembered, some remembered ∈ memories owner ∧ remembered.event = query) ∨
        saved.map Completion.event = some query := by
  constructor
  · rintro ⟨owner, remembered, retained, named⟩
    by_cases equal : owner = who
    · subst owner
      rw [Function.update_self] at retained
      rcases List.mem_append.mp retained with earlier | current
      · exact Or.inl ⟨who, remembered, earlier, named⟩
      · right
        have selected : some remembered = saved := List.mem_singleton.mp current
        rw [← selected]
        exact congrArg some named
    · rw [Function.update_of_ne equal] at retained
      exact Or.inl ⟨owner, remembered, retained, named⟩
  · rintro (⟨owner, remembered, retained, named⟩ | selected)
    · refine ⟨owner, remembered, ?_, named⟩
      by_cases equal : owner = who
      · subst owner
        rw [Function.update_self]
        exact List.mem_append_left _ retained
      · rw [Function.update_of_ne equal]
        exact retained
    · cases saved with
      | none => cases selected
      | some remembered =>
          exact ⟨who, remembered, by simp, Option.some.inj selected⟩

end Vegas.EventGraphRuntime
