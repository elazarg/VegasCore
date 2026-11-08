/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.SchedulerErasure
import Vegas.EventGraph.Sequential

/-! # Scheduling graphs whose only concurrency is between reveals

Relaxing the reveal dependencies of a totally ordered graph makes exactly the
independent reveals concurrent: two simultaneously ready events are always
independent reveals of different owners. A foreign reveal can complete before a
reveal's own kernel acts, so a profile is scheduler independent only when its
kernels ignore the observation at publications, for example a profile that
always opens. Normalizing such a profile makes it ready independent, so its
law of the final store and completion records is the same under every public
scheduler.

Bindings stay ordered. Concurrent bindings would not be ready independent:
an omitted binding is public, so a binder scheduled later could react to it.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- Two simultaneously ready events are always independent reveals. -/
def RevealsOnlyConcurrent : Prop :=
  ∀ (cut : graph.order.Cut) {left right : graph.EventId}, cut.Ready left → cut.Ready right →
    left ≠ right → graph.IndependentReveals left right ∨ graph.IndependentReveals right left

omit [DecidableEq Player] in
/-- Relaxing the reveal dependencies of a totally ordered graph makes only reveals concurrent. -/
theorem withMode_concurrentReveals_revealsOnlyConcurrent
    (graph : Vegas.EventGraph Player L)
    (total : ∀ prior event : graph.EventId, prior.val < event.val →
      prior ∈ graph.order.predecessors event) :
    (graph.withMode .concurrentReveals).RevealsOnlyConcurrent := by
  intro cut left right leftReady rightReady different
  have independent (prior event : graph.EventId) (earlier : prior.val < event.val)
      (priorReady : cut.Ready prior) (eventReady : cut.Ready event) :
      graph.IndependentReveals prior event := by
    by_contra dependent
    exact priorReady.1 (eventReady.2
      ((graph.withMode_concurrentReveals_predecessors prior event).mpr
        ⟨total prior event earlier, dependent⟩))
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne different) with earlier | later
  · exact Or.inl (independent left right earlier leftReady rightReady)
  · exact Or.inr (independent right left later rightReady leftReady)

omit [DecidableEq Player] in
theorem IndependentReveals.actorsDiffer {prior event : graph.EventId}
    (independent : graph.IndependentReveals prior event) : graph.ActorsDiffer prior event :=
  fun _ priorActor eventActor => independent.2.2.2 (priorActor.trans eventActor.symm)

variable (graph) in
/-- At every publication the profile's kernel ignores the observation. -/
def ObliviousAtPublications (profile : graph.BehavioralProfile) : Prop :=
  ∀ who event (actor : graph.actor? event = some who),
    (graph.outputLayout event).IsPublication →
      ∀ (left right : graph.PlayerObservation who) leftActive rightActive,
        profile who event actor left leftActive = profile who event actor right rightActive

private theorem policy_congr {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : graph.actor? event = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

/-- **Ready independence on reveal-only concurrency.** A normalized profile
that ignores the observation at publications is ready independent. -/
theorem RevealsOnlyConcurrent.readyIndependent_normalizeProfile
    (only : graph.RevealsOnlyConcurrent) (profile : graph.BehavioralProfile)
    (oblivious : graph.ObliviousAtPublications profile) :
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
          exact oblivious owner event ownerEq publication _ _ _ _
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

/-- **Scheduler erasure for concurrent reveals.** Under every public scheduler,
the normalization of a profile that ignores the observation at publications has
the canonical law of the final store and completion records. -/
theorem RevealsOnlyConcurrent.runPolicies_map_runKey (only : graph.RevealsOnlyConcurrent)
    (profile : graph.BehavioralProfile) (oblivious : graph.ObliviousAtPublications profile)
    (scheduler : graph.PublicScheduler) (inputs : graph.Inputs) :
    (graph.runPolicies scheduler (graph.normalizeProfile profile) inputs).map runKey =
      (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) inputs).map
        runKey :=
  (only.readyIndependent_normalizeProfile profile oblivious).runPolicies_map_runKey scheduler inputs

end Vegas.EventGraph
