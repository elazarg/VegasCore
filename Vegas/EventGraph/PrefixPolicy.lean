module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.RevealRelaxedScheduling

@[expose] public section

/-! # Source-prefix policies for concurrent commitments

Prescribed policies see source-ranked prefix slots and their own earlier actions.
Private binding slots carry no default marker, including slots that have not yet
completed. Public default markers remain visible. Actual observations and the
policies available to deviators retain the complete chronological information.

For profiles that ignore observations at publications, this projection makes
the final store and individual completion records independent of public scheduling
under the existing reveal-relaxed barrier discipline.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- The source-ranked events before a decision. -/
def decisionPrefix (event : graph.EventId) : List graph.EventId :=
  (List.finRange graph.order.eventCount).filter fun prior => prior.val < event.val

variable (graph) in
/-- A prescribed decision sees its source prefix. Private-binding completions
contribute a no-default slot even when the scheduler has not completed them. -/
def prefixObservation (who : Player) (event : graph.EventId)
    (observation : graph.PlayerObservation who) : graph.PlayerObservation who where
  completionOrder := graph.decisionPrefix event
  store := observation.store
  ownActions := (graph.normalizeObservation who observation).ownActions.filter fun completion =>
    completion.event.val < event.val
  defaults := ⟨((graph.decisionPrefix event).map fun prior =>
    if (graph.outputLayout prior).IsPublic then graph.observedDefaultOf observation prior
    else none).reverse⟩

theorem prefixObservation_defaulted_subset (who : Player) (event : graph.EventId)
    (observation : graph.PlayerObservation who) :
    (graph.prefixObservation who event observation).defaulted ⊆ observation.defaulted := by
  intro owner member
  simp only [EventPlayerObservation.defaulted, DefaultHistory.defaulted, prefixObservation,
    List.mem_toFinset, List.mem_filterMap, List.mem_reverse, List.mem_map, id_eq] at member ⊢
  obtain ⟨_, ⟨prior, _, found⟩, rfl⟩ := member
  split at found
  · simp only [observedDefaultOf, Option.bind_eq_some_iff] at found
    obtain ⟨entry, entryFound, entryDefault⟩ := found
    have entryMember := List.mem_of_find?_eq_some entryFound
    have := (List.of_mem_zip entryMember).2
    exact ⟨entry.2, by rwa [List.mem_reverse] at this, entryDefault⟩
  · cases found

variable (graph) in
/-- Compile a policy through its source-prefix observation. -/
def prefixPolicy (who : Player) (policy : graph.BehavioralPolicy who) :
    graph.BehavioralPolicy who :=
  fun event actor observation active =>
    policy event actor (graph.prefixObservation who event observation)
      (fun member => active (prefixObservation_defaulted_subset who event observation member))

variable (graph) in
/-- Compile a profile through source-prefix observations. -/
def prefixProfile (profile : graph.BehavioralProfile) : graph.BehavioralProfile :=
  fun who => graph.prefixPolicy who (profile who)

theorem observedDefaultOf_playerObserve (who : Player) (config : graph.Config)
    (event : graph.EventId) :
    graph.observedDefaultOf (graph.playerObserve who config) event =
      (completionOf config event).bind EventCompletion.defaultEvent := by
  unfold observedDefaultOf
  change (((config.history.map EventCompletion.event).zip
    (EventCompletion.defaults config.history).events.reverse).find? _).bind _ = _
  simp only [EventCompletion.defaults, List.reverse_reverse]
  rw [find?_zip_map]
  unfold completionOf
  cases config.history.find? (fun completion => completion.event = event) <;> rfl

theorem prefixObservation_playerObserve_congr (who : Player) (event : graph.EventId)
    {left right : graph.Config} (same : graph.storeRecall left = graph.storeRecall right) :
    graph.prefixObservation who event (graph.playerObserve who left) =
      graph.prefixObservation who event (graph.playerObserve who right) := by
  have normalized := graph.normalizeObservation_playerObserve_congr who same
  have stores := congrArg EventPlayerObservation.store normalized
  have own := congrArg EventPlayerObservation.ownActions normalized
  have records : completionOf left = completionOf right := congrArg Prod.snd same
  apply EventPlayerObservation.ext
  · rfl
  · exact stores
  · exact congrArg (List.filter _) own
  · simp only [prefixObservation, observedDefaultOf_playerObserve, records]

theorem prefixObservation_playerObserve_complete_of_hidden (who : Player)
    (config : graph.Config) (event other : graph.EventId) (ready : config.cut.Ready other)
    (action : graph.Action other) (value : (graph.outputLayout other).Value)
    (hidden : ¬ graph.fieldVisibleTo who (.inr other))
    (notOwned : graph.actor? other ≠ some who)
    (privateOutput : ¬ (graph.outputLayout other).IsPublic) :
    graph.prefixObservation who event
        (graph.playerObserve who (config.complete other ready action value)) =
      graph.prefixObservation who event (graph.playerObserve who config) := by
  apply EventPlayerObservation.ext
  · rfl
  · exact graph.playerStore_complete_of_hidden who config other ready action value hidden
  · have own := graph.ownCompletions_complete_of_not_actor who config other ready action value
      notOwned
    simp only [prefixObservation, normalizeObservation, playerObserve, own]
  · unfold prefixObservation
    simp only [observedDefaultOf_playerObserve]
    congr 2
    apply List.map_congr_left
    intro prior _
    by_cases same : prior = other
    · subst prior
      simp [privateOutput]
    · rw [completionOf_complete, Function.update_of_ne same]

private theorem policy_congr {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : graph.actor? event = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

theorem RevealRelaxedOrdered.readyIndependent_prefixProfile
    (relaxed : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (oblivious : graph.ObliviousAtPublications profile) :
    ReadyIndependent (graph.prefixProfile profile) where
  actorsDiffer config left right leftReady rightReady different := by
    obtain ⟨leftOwner, rightOwner, leftActor, rightActor, distinct⟩ :=
      relaxed.ready_pair_actors leftReady rightReady different
    intro owner owned otherOwned
    have same : leftOwner = owner := Option.some.inj (leftActor.symm.trans owned)
    have otherSame : rightOwner = owner := Option.some.inj (rightActor.symm.trans otherOwned)
    exact distinct (same.trans otherSame.symm)
  stable config event other eventReady otherReady different action value := by
    obtain ⟨owner, otherOwner, actor, otherActor, distinct⟩ :=
      relaxed.ready_pair_actors eventReady otherReady different.symm
    rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
    have notOwned : graph.actor? other ≠ some owner := by
      rw [otherActor]
      simpa using Ne.symm distinct
    have member := mem_defaulted_complete_of_actor_ne config other otherReady action value
      owner notOwned
    by_cases inactive : owner ∈ config.defaulted
    · rw [dite_eq_left (member.mpr inactive), dite_eq_left inactive]
    · rw [dite_eq_right (fun active => inactive (member.mp active)), dite_eq_right inactive]
      change profile owner event actor _ _ = profile owner event actor _ _
      by_cases publication : (graph.outputLayout event).IsPublication
      · exact oblivious owner event actor publication _ _ _ _
      · have privateOutput : ¬ (graph.outputLayout other).IsPublic := by
          intro isPublic
          exact publication (relaxed.ready_public_pair_publications config.cut eventReady
            otherReady different.symm (Or.inr isPublic)).1
        have hidden : ¬ graph.fieldVisibleTo owner (.inr other) := by
          rcases EventCode.output_public_or_binding_of_actor (graph.nodes other) otherOwner
              otherActor with isPublic | ⟨payload, binding⟩
          · exact (privateOutput isPublic).elim
          · unfold fieldVisibleTo
            change ¬ (graph.outputLayout other).VisibleTo owner
            rw [binding]
            simpa [EventField.VisibleTo] using Ne.symm distinct
        exact policy_congr _ event actor
          (prefixObservation_playerObserve_complete_of_hidden owner config event other
            otherReady action value hidden notOwned privateOutput) _ _
  congr {left right} same event := by
    have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
    have defaulted := defaulted_eq_of_completionOf_eq records
    cases ownerEq : (graph.nodes event).actor with
    | none => rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
    | some owner =>
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
        by_cases inactive : owner ∈ left.defaulted
        · rw [dite_eq_left inactive, dite_eq_left (defaulted ▸ inactive)]
        · rw [dite_eq_right inactive, dite_eq_right (defaulted ▸ inactive)]
          change profile owner event ownerEq _ _ = profile owner event ownerEq _ _
          exact policy_congr _ event ownerEq
            (prefixObservation_playerObserve_congr owner event (congrArg Prod.snd same)) _ _

theorem RevealRelaxedOrdered.runPolicies_prefixProfile_map_runKey
    (relaxed : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (oblivious : graph.ObliviousAtPublications profile)
    (scheduler : graph.PublicScheduler) (inputs : graph.Inputs) :
    (graph.runPolicies scheduler (graph.prefixProfile profile) inputs).map runKey =
      (graph.runPolicies graph.canonicalScheduler (graph.prefixProfile profile) inputs).map
        runKey :=
  (relaxed.readyIndependent_prefixProfile profile oblivious).runPolicies_map_runKey scheduler
    inputs

end Vegas.EventGraph
