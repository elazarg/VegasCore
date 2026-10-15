/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.RelaxedRecall
import Vegas.EventGraph.ObservationStep

/-! # Semantic observations at a surviving ready binding -/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Relaxed revelation ordering retains the exact ranked owned event prefix. -/
theorem RevealRelaxedOrdered.ready_ownEventIds
    (ordered : graph.RevealRelaxedOrdered) {inputs : graph.Inputs} {config : graph.Config}
    (reachable : config.Reachable inputs) {event : graph.EventId} {who : Player}
    (ready : config.cut.Ready event) (actor : graph.actor? event = some who) :
    graph.ownEventIds who config.history = graph.prefixSchema.ownHistory event := by
  have ranked : (graph.prefixSchema.ownHistory event).Pairwise
      (fun left right => left.val < right.val) := by
    simpa [prefixSchema, actor] using
      (List.sortedLT_finRange graph.order.eventCount).pairwise.filter
        (fun prior => decide (prior.val < event.val ∧ graph.actor? prior = some who))
  apply (ordered.ownEventIds_pairwise reachable who).eq_of_mem_iff ranked
  intro prior
  have actual : (graph.ownEventIds who config.history).toFinset =
      graph.completedOwnEvents who config.cut := by
    ext query
    simp only [ownEventIds, ownCompletions, List.mem_toFinset, List.mem_map, List.mem_filter,
      completedOwnEvents, Finset.mem_filter]
    constructor
    · rintro ⟨completion, ⟨present, owned⟩, rfl⟩
      exact ⟨(config.history_exact completion.event).mp
        (List.mem_map.mpr ⟨completion, present, rfl⟩), of_decide_eq_true owned⟩
    · rintro ⟨completed, owned⟩
      obtain ⟨completion, present, same⟩ :=
        List.mem_map.mp ((config.history_exact query).mpr completed)
      exact ⟨completion, ⟨present, by simp only [same, owned, decide_true]⟩, same⟩
  have sets := actual.trans (ordered.ready_own_history_exact config.cut ready actor).symm
  simpa only [List.mem_toFinset] using
    Iff.of_eq (congrArg (fun set : Finset graph.EventId => prior ∈ set) sets)

/-- Hidden foreign completions may change chronological metadata, while the
visible store and every original owned action at the retained binding stay exact. -/
theorem RevealRelaxedOrdered.ready_semantics_eq_of_extension
    (ordered : graph.RevealRelaxedOrdered) {inputs : graph.Inputs}
    (before after : graph.Config) (beforeReachable : before.Reachable inputs)
    (afterReachable : after.Reachable inputs) (who : Player) (event : graph.EventId)
    (beforeReady : before.cut.Ready event) (afterReady : after.cut.Ready event)
    (actor : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (stored : ∀ field value, before.store field = some value → after.store field = some value)
    (retained : before.history.IsPrefix after.history) :
    graph.playerStore who after.store = graph.playerStore who before.store ∧
      graph.ownCompletions who after.history = graph.ownCompletions who before.history := by
  refine ⟨?_, ?_⟩
  · apply graph.playerStore_congr
    intro field visible
    have available : (before.store field).isSome = (after.store field).isSome := by
      cases field with
      | inl input => rfl
      | inr query =>
          apply Bool.eq_iff_iff.mpr
          simp only [Config.store_output, before.output_available, after.output_available]
          exact (ordered.ready_visible_iff before.cut beforeReady actor visible
            (IndependentReveals.not_of_not_publication_right notPublication)
            (IndependentReveals.not_of_not_publication_left notPublication)).trans
              (ordered.ready_visible_iff after.cut afterReady actor visible
                (IndependentReveals.not_of_not_publication_right notPublication)
                (IndependentReveals.not_of_not_publication_left notPublication)).symm
    cases found : before.store field with
    | none =>
        cases later : after.store field with
        | none => rfl
        | some value => simp only [found, later, Option.isSome_none, Option.isSome_some,
            Bool.false_eq_true] at available
    | some value => rw [stored field value found]
  · have ids := (ordered.ready_ownEventIds beforeReachable beforeReady actor).trans
      (ordered.ready_ownEventIds afterReachable afterReady actor).symm
    have lengths := congrArg List.length ids
    simp only [ownEventIds, List.length_map] at lengths
    have kept := retained.filter
      (fun completion => decide (graph.actor? completion.event = some who))
    change (graph.ownCompletions who before.history).IsPrefix
      (graph.ownCompletions who after.history) at kept
    rw [List.prefix_iff_eq_take, lengths, List.take_length] at kept
    exact kept.symm

end Vegas.EventGraph
