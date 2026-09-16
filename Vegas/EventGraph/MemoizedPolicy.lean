/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulerErasure

/-! # Canonical continuations with memoized actions -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A canonical continuation only consults policy coordinates belonging to
unfinished events. -/
theorem canonicalContinuation_congr_on_unfinished
    (left right : graph.BehavioralProfile) (config : graph.Config)
    (agree : ∀ event, event ∉ config.cut.completed → ∀ who actor observation,
      graph.normalizePolicy who (left who) event actor observation =
        graph.normalizePolicy who (right who) event actor observation) :
    graph.canonicalContinuation left config =
      graph.canonicalContinuation right config := by
  generalize remainingEq : config.remaining = remaining
  induction remaining using Nat.strong_induction_on generalizing config with
  | h remaining ih =>
      by_cases terminal : config.cut.Terminal
      · rw [← graph.canonicalContinuation_terminal left config terminal,
          ← graph.canonicalContinuation_terminal right config terminal]
      · let event := config.cut.enabled.min'
          (enabled_nonempty_of_not_terminal config terminal)
        have ready : config.cut.Ready event :=
          (EventOrder.Cut.mem_enabled _ _).mp
            (Finset.min'_mem _ (enabled_nonempty_of_not_terminal config terminal))
        have least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val :=
          (canonical_min_ready_is_least_unfinished config.cut terminal).2
        rw [canonicalContinuation_step left config event ready least,
          canonicalContinuation_step right config event ready least]
        unfold normalizedThenCanonical normalizedPolicyStep
        split
        · rename_i who actor
          rw [agree event ready.1 who actor (graph.playerObserve who config)]
          apply FinDist.bind_congr
          intro next member
          simp only [FinDist.support_bind, Set.mem_iUnion] at member
          obtain ⟨action, _, member⟩ := member
          apply ih next.remaining
          · have decreased := config.remaining_step event ready action next member
            omega
          · intro other unfinished owner otherActor observation
            apply agree other
            intro completed
            apply unfinished
            rw [config.step_cut event ready action next member]
            exact config.cut.completed_subset_complete event ready completed
          · rfl
        · rename_i ownerless
          apply FinDist.bind_congr
          intro next member
          apply ih next.remaining
          · have decreased := config.remaining_step event ready
                (EventCode.actionOfActorNone (graph.nodes event) ownerless) next member
            omega
          · intro other unfinished owner otherActor observation
            apply agree other
            intro completed
            apply unfinished
            rw [config.step_cut event ready
              (EventCode.actionOfActorNone (graph.nodes event) ownerless) next member]
            exact config.cut.completed_subset_complete event ready completed
          · rfl

/-- Override a normalized graph profile by actions already sampled for
particular events. -/
def memoizedProfile (profile : graph.BehavioralProfile)
    (remembered : (event : graph.EventId) → Option (graph.Action event)) :
    graph.BehavioralProfile :=
  fun who event actor observation =>
    match remembered event with
    | some action => FinDist.pure action
    | none => graph.normalizePolicy who (profile who) event actor observation

omit [DecidableEq Player] in
@[simp] theorem normalizePolicy_memoizedProfile
    (profile : graph.BehavioralProfile)
    (remembered : (event : graph.EventId) → Option (graph.Action event))
    (who : Player) (event : graph.EventId) (actor : graph.actor? event = some who)
    (observation : graph.PlayerObservation who) :
    graph.normalizePolicy who (graph.memoizedProfile profile remembered who)
        event actor observation =
      graph.memoizedProfile profile remembered who event actor observation := by
  cases saved : remembered event with
  | some action => simp [memoizedProfile, normalizePolicy, saved]
  | none =>
      simp only [normalizePolicy, memoizedProfile, saved]
      exact congrFun (congrFun (congrFun
        (graph.normalizePolicy_idempotent who (profile who)) event) actor) observation

/-- Changing a memo table only at completed events leaves the continuation
law unchanged. -/
theorem canonicalContinuation_memoized_congr_on_unfinished
    (profile : graph.BehavioralProfile)
    (left right : (event : graph.EventId) → Option (graph.Action event))
    (config : graph.Config)
    (agree : ∀ event, event ∉ config.cut.completed → left event = right event) :
    graph.canonicalContinuation (graph.memoizedProfile profile left) config =
      graph.canonicalContinuation (graph.memoizedProfile profile right) config := by
  apply canonicalContinuation_congr_on_unfinished
    (graph.memoizedProfile profile left) (graph.memoizedProfile profile right) config
  intro event unfinished who actor observation
  rw [normalizePolicy_memoizedProfile, normalizePolicy_memoizedProfile,
    memoizedProfile, memoizedProfile, agree event unfinished]

/-- If an event has a saved action, its canonical continuation exposes exactly
that fixed semantic step, regardless of its position in the ready set. -/
theorem BarrierOrdered.canonicalContinuation_memoized_step
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (remembered : (event : graph.EventId) → Option (graph.Action event))
    (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (who : Player)
    (actor : graph.actor? event = some who) (action : graph.Action event)
    (saved : remembered event = some action) :
    graph.canonicalContinuation (graph.memoizedProfile profile remembered) config =
      (config.step event ready action).bind
        (graph.canonicalContinuation (graph.memoizedProfile profile remembered)) := by
  rw [← ordered.normalizedThenCanonical_eq
    (graph.memoizedProfile profile remembered) config event ready]
  unfold normalizedThenCanonical normalizedPolicyStep
  split
  · rename_i actual actualActor
    have ownerEq : actual = who := Option.some.inj (actualActor.symm.trans actor)
    subst actual
    rw [normalizePolicy_memoizedProfile]
    simp [memoizedProfile, saved]
  · rename_i ownerless
    simp [actor] at ownerless

/-- Sampling and saving a previously unmemoized ready action preserves the
canonical continuation law exactly. -/
theorem BarrierOrdered.canonicalContinuation_remember
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (remembered : (event : graph.EventId) → Option (graph.Action event))
    (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (who : Player)
    (actor : graph.actor? event = some who) (empty : remembered event = none) :
    graph.canonicalContinuation (graph.memoizedProfile profile remembered) config =
      (graph.normalizePolicy who (profile who) event actor
        (graph.playerObserve who config)).bind fun action =>
          graph.canonicalContinuation
            (graph.memoizedProfile profile
              (Function.update remembered event (some action))) config := by
  rw [← ordered.normalizedThenCanonical_eq
    (graph.memoizedProfile profile remembered) config event ready]
  unfold normalizedThenCanonical normalizedPolicyStep
  split
  · rename_i actual actualActor
    have ownerEq : actual = who := Option.some.inj (actualActor.symm.trans actor)
    subst actual
    rw [normalizePolicy_memoizedProfile]
    simp only [memoizedProfile, empty]
    rw [FinDist.bind_bind]
    apply FinDist.bind_congr
    intro action _
    rw [ordered.canonicalContinuation_memoized_step profile
      (Function.update remembered event (some action)) config event ready who actor action
      (by simp)]
    apply FinDist.bind_congr
    intro next member
    apply graph.canonicalContinuation_memoized_congr_on_unfinished profile
    intro query unfinished
    by_cases same : query = event
    · subst query
      exact False.elim (unfinished (by
        rw [config.step_cut event ready action next member]
        simp))
    · simp [Function.update, same]
  · rename_i ownerless
    simp [actor] at ownerless

end Vegas.EventGraph
