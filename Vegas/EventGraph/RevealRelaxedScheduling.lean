/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulerErasure
import Vegas.EventGraph.ExecutionMode

/-! # Scheduling reveal-relaxed graphs

On a reveal-relaxed graph two simultaneously ready events are either bindings
of different owners, each hidden from the other's actor, or independent
reveals, each of whose outputs is public. A reveal kernel may therefore see a
foreign reveal of its block complete before it acts. For a profile whose reveal
kernels ignore the observation, for example one that always opens, that is
invisible, and every adaptive public scheduler gives the canonical terminal
store law. At every event that is not a reveal the normalized observation is
exactly the source-prefix logical observation, as under public barriers.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A profile whose kernel at every reveal ignores the observation, as one that
always opens does. -/
def ObliviousAtPublications (profile : graph.BehavioralProfile) : Prop :=
  ∀ who event (actor : graph.actor? event = some who),
    (graph.outputLayout event).IsPublication →
      ∀ left right : graph.PlayerObservation who,
        profile who event actor left = profile who event actor right

/-- At a ready strategic event that is not a reveal, normalization changes only
completion-order metadata: the retained store and own actions are the
source-prefix logical observation. -/
theorem RevealRelaxedOrdered.normalizeObservation_eq_logical
    (relaxed : graph.RevealRelaxedOrdered)
    (config : graph.Config) (event : graph.EventId) (who : Player)
    (ready : config.cut.Ready event) (actor : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication) :
    graph.normalizeObservation event who (graph.playerObserve who config) =
      { completionOrder := graph.rankPrefix event
        store := (graph.logicalObserve graph.prefixSchema event who
          (graph.playerObserve who config)).store
        ownActions := (graph.logicalObserve graph.prefixSchema event who
          (graph.playerObserve who config)).ownActions } := by
  apply PlayerObservation.ext graph
  · rfl
  · exact (logicalObserve_store_of_fields_exact config event who
      (relaxed.ready_fields_exact config.cut ready actor notPublication)).symm
  · exact (logicalObserve_ownActions_of_history_exact config event who
      (relaxed.ready_own_history_exact config.cut ready actor)).symm

/-- On a reveal-relaxed graph every profile that ignores observations at reveals
is ready independent: a simultaneously ready foreign binding is hidden, and a
simultaneously ready foreign reveal meets a reveal kernel that ignores it. -/
theorem RevealRelaxedOrdered.readyIndependent (relaxed : graph.RevealRelaxedOrdered)
    {profile : graph.BehavioralProfile} (oblivious : ObliviousAtPublications profile) :
    graph.ReadyIndependent profile where
  ready_pair_actors := relaxed.ready_pair_actors
  normalizePolicy_complete_foreign config event other eventReady otherReady who actor foreign
      otherActor differentOwner action value := by
    have different : event ≠ other := by
      intro same
      subst same
      rw [actor] at otherActor
      exact differentOwner (Option.some.inj otherActor).symm
    by_cases publication : (graph.outputLayout event).IsPublication
    · exact oblivious who event actor publication _ _
    · have otherPrivate : ¬ (graph.outputLayout other).IsPublic := by
        intro otherPublic
        exact publication (relaxed.ready_public_pair_publications config.cut eventReady
          otherReady different (Or.inr otherPublic)).1
      have hidden : ¬ graph.fieldVisibleTo who (.inr other) := by
        intro visible
        change (graph.outputLayout other).VisibleTo who at visible
        have visibleForeign : (graph.outputLayout other).VisibleTo foreign :=
          EventCode.output_visible_of_actor (graph.nodes other) foreign otherActor
        cases kind : graph.outputLayout other <;>
          simp_all [EventField.IsPublic, EventField.VisibleTo]
      have storeEq := graph.playerStore_complete_of_hidden who config other otherReady
        action value hidden
      have notOwned : graph.actor? other ≠ some who := by
        rw [otherActor]
        simpa using differentOwner
      have actionsEq := graph.ownCompletions_complete_of_not_actor who config other
        otherReady action value notOwned
      apply congrArg (profile who event actor)
      apply PlayerObservation.ext graph
      · rfl
      · exact storeEq
      · exact actionsEq

/-- Every adaptive public scheduler gives a reveal-relaxed graph the canonical
terminal store law, for every profile that ignores observations at reveals. -/
theorem RevealRelaxedOrdered.runPolicies_store_eq_canonical
    (relaxed : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (oblivious : ObliviousAtPublications profile)
    (scheduler : graph.PublicScheduler) (inputs : graph.Inputs) :
    (graph.runPolicies scheduler (graph.normalizeProfile profile) inputs).map
        Config.store =
      (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) inputs).map
        Config.store :=
  (relaxed.readyIndependent oblivious).runPolicies_store_eq_canonical scheduler inputs

/-- Running a public-barrier graph with independent reveals concurrent, under any
adaptive public scheduler, gives a profile that ignores observations at reveals
the canonical terminal store law of the original graph. -/
theorem runPolicies_concurrentReveals_store (graph : Vegas.EventGraph Player L)
    (ordered : graph.BarrierOrdered)
    (profile : (graph.withMode .concurrentReveals).BehavioralProfile)
    (oblivious : ObliviousAtPublications profile)
    (scheduler : (graph.withMode .concurrentReveals).PublicScheduler)
    (inputs : graph.Inputs) :
    ((graph.withMode .concurrentReveals).runPolicies scheduler
        ((graph.withMode .concurrentReveals).normalizeProfile profile) inputs).map
        Config.store =
      (graph.runPolicies graph.canonicalScheduler
        (graph.fromModeProfile .concurrentReveals profile) inputs).map Config.store := by
  rw [(graph.withMode_revealRelaxedOrdered ordered .concurrentReveals
      ).runPolicies_store_eq_canonical profile oblivious scheduler inputs,
    ← runPolicies_canonical_normalize_eq]
  exact graph.runPolicies_withMode_store .concurrentReveals profile inputs

end Vegas.EventGraph
