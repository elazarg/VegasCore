module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.RevealRelaxedScheduling
public import Vegas.EventGraph.LastSchedulerErasure

@[expose] public section

/-! # Ready independence from read footprints

A profile is footprint oblivious at publications when its kernel at a
publication depends on the observation only through the observed store on the
publication's read footprint. That footprint has completed whenever the
publication is ready, so completing a concurrently ready event leaves it
unchanged. On a graph whose only concurrency is between independent reveals,
the normalization of such a profile is therefore ready independent, and away
from one player when only the other players are footprint oblivious.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- The kernels of the selected owners at publications read only the observed
store on the publication's read footprint. -/
def FootprintOblivious (profile : graph.BehavioralProfile) (owners : Player → Prop) : Prop :=
  ∀ owner, owners owner → ∀ event (actor : graph.actor? event = some owner),
    (graph.outputLayout event).IsPublication →
      ∀ (left right : graph.PlayerObservation owner) leftActive rightActive,
        Store.AgreeOn left.store right.store (graph.nodes event).readFields →
          profile owner event actor left leftActive = profile owner event actor right rightActive

omit [DecidableEq Player] in
/-- A concurrently ready event is not read by a ready event. -/
theorem not_mem_readFields_of_ready {config : graph.Config} {event other : graph.EventId}
    (eventReady : config.cut.Ready event) (otherReady : config.cut.Ready other) :
    (.inr other : graph.Field) ∉ (graph.nodes event).readFields := fun read =>
  otherReady.1 (eventReady.2 (graph.reads_available event (.inr other) read))

/-- Completing a concurrently ready event leaves every player's observed store
unchanged on a ready event's read footprint. -/
theorem playerStore_complete_agreeOn (who : Player) (config : graph.Config)
    {event other : graph.EventId} (eventReady : config.cut.Ready event)
    (otherReady : config.cut.Ready other) (action : graph.Action other)
    (value : (graph.outputLayout other).Value) :
    Store.AgreeOn (graph.playerStore who (config.complete other otherReady action value).store)
      (graph.playerStore who config.store) (graph.nodes event).readFields := by
  intro field read
  have different : field ≠ .inr other := by
    rintro rfl
    exact not_mem_readFields_of_ready eventReady otherReady read
  simp only [playerStore, store_complete, Function.update_of_ne different]

private theorem policy_congr {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : graph.actor? event = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

/-- The kernel of a footprint-oblivious owner at a ready publication is
unchanged by completing a concurrently ready event. -/
private theorem normalize_footprint_stable (profile : graph.BehavioralProfile)
    {owners : Player → Prop} (footprint : graph.FootprintOblivious profile owners)
    (config : graph.Config) {event other : graph.EventId} (eventReady : config.cut.Ready event)
    (otherReady : config.cut.Ready other) (action : graph.Action other)
    (value : (graph.outputLayout other).Value) {owner : Player} (selected : owners owner)
    (ownerEq : (graph.nodes event).actor = some owner)
    (publication : (graph.outputLayout event).IsPublication)
    (leftActive : owner ∉ (graph.playerObserve owner
      (config.complete other otherReady action value)).defaulted)
    (rightActive : owner ∉ (graph.playerObserve owner config).defaulted) :
    graph.normalizeProfile profile owner event ownerEq
        (graph.playerObserve owner (config.complete other otherReady action value)) leftActive =
      graph.normalizeProfile profile owner event ownerEq (graph.playerObserve owner config)
        rightActive :=
  footprint owner selected event ownerEq publication _ _ _ _
    (playerStore_complete_agreeOn owner config eventReady otherReady action value)

/-- **Footprint-oblivious normalizations are ready independent.** -/
theorem RevealsOnlyConcurrent.readyIndependent_normalizeProfile_of_footprint
    (only : graph.RevealsOnlyConcurrent) (profile : graph.BehavioralProfile)
    (footprint : graph.FootprintOblivious profile fun _ => True) :
    ReadyIndependent (graph.normalizeProfile profile) where
  actorsDiffer config left right leftReady rightReady different := by
    rcases only config.cut leftReady rightReady different with independent | independent
    · exact independent.actorsDiffer
    · exact independent.actorsDiffer.symm
  stable config event other eventReady otherReady different action value := by
    have independent : graph.IndependentReveals other event ∨
        graph.IndependentReveals event other :=
      only config.cut otherReady eventReady different
    have publication : (graph.outputLayout event).IsPublication := by
      rcases independent with independent | independent
      · exact independent.2.1
      · exact independent.1
    have actorsNe : graph.actor? other ≠ graph.actor? event := by
      rcases independent with independent | independent
      · exact independent.2.2.2
      · exact Ne.symm independent.2.2.2
    cases ownerEq : (graph.nodes event).actor with
    | none =>
        rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
    | some owner =>
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
        have member := mem_defaulted_complete_of_actor_ne config other otherReady action value
          owner (fun otherActor => actorsNe (otherActor.trans ownerEq.symm))
        by_cases inactive : owner ∈ config.defaulted
        · rw [dite_eq_left (member.mpr inactive), dite_eq_left inactive]
        · rw [dite_eq_right (fun active => inactive (member.mp active)),
            dite_eq_right inactive]
          exact normalize_footprint_stable profile footprint config eventReady otherReady action
            value trivial ownerEq publication _ _
  congr {left right} same event := by
    have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
    have defaulted := defaulted_eq_of_completionOf_eq records
    cases ownerEq : (graph.nodes event).actor with
    | none =>
        rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
    | some owner =>
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
        by_cases inactive : owner ∈ left.defaulted
        · rw [dite_eq_left inactive, dite_eq_left (defaulted ▸ inactive)]
        · rw [dite_eq_right inactive, dite_eq_right (defaulted ▸ inactive)]
          exact policy_congr _ event ownerEq
            (graph.normalizeObservation_playerObserve_congr owner (congrArg Prod.snd same)) _ _

/-- **Footprint-oblivious normalizations are ready independent away from one
player.** Only the other players need to be footprint oblivious. -/
theorem RevealsOnlyConcurrent.lastIndependent_normalizeProfile_of_footprint
    (only : graph.RevealsOnlyConcurrent) (profile : graph.BehavioralProfile) (who : Player)
    (footprint : graph.FootprintOblivious profile fun owner => owner ≠ who) :
    LastIndependent (graph.normalizeProfile profile) who where
  actorsDiffer config left right leftReady rightReady different := by
    rcases only config.cut leftReady rightReady different with independent | independent
    · exact independent.actorsDiffer
    · exact independent.actorsDiffer.symm
  stable config event other eventReady otherReady different movable action value := by
    have independent : graph.IndependentReveals other event ∨
        graph.IndependentReveals event other :=
      only config.cut otherReady eventReady different
    have publication : (graph.outputLayout event).IsPublication := by
      rcases independent with independent | independent
      · exact independent.2.1
      · exact independent.1
    have actorsNe : graph.actor? other ≠ graph.actor? event := by
      rcases independent with independent | independent
      · exact independent.2.2.2
      · exact Ne.symm independent.2.2.2
    cases ownerEq : (graph.nodes event).actor with
    | none =>
        rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
    | some owner =>
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
        have member := mem_defaulted_complete_of_actor_ne config other otherReady action value
          owner (fun otherActor => actorsNe (otherActor.trans ownerEq.symm))
        by_cases inactive : owner ∈ config.defaulted
        · rw [dite_eq_left (member.mpr inactive), dite_eq_left inactive]
        · rw [dite_eq_right (fun active => inactive (member.mp active)),
            dite_eq_right inactive]
          have ownerNe : owner ≠ who := by
            rintro rfl
            rcases movable with foreign | defaulted
            · exact foreign ownerEq
            · exact inactive defaulted
          exact normalize_footprint_stable profile footprint config eventReady otherReady action
            value ownerNe ownerEq publication _ _
  congr {left right} same event := by
    have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
    have defaulted := defaulted_eq_of_completionOf_eq records
    cases ownerEq : (graph.nodes event).actor with
    | none =>
        rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
    | some owner =>
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
        by_cases inactive : owner ∈ left.defaulted
        · rw [dite_eq_left inactive, dite_eq_left (defaulted ▸ inactive)]
        · rw [dite_eq_right inactive, dite_eq_right (defaulted ▸ inactive)]
          exact policy_congr _ event ownerEq
            (graph.normalizeObservation_playerObserve_congr owner (congrArg Prod.snd same)) _ _

end Vegas.EventGraph
