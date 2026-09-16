/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulingLaw

/-! # Erasing honest public scheduling choices

Normalized policies factor through the semantic state consisting of the cut,
typed store, and per-player original-action recall.  Public-barrier local
confluence then makes the terminal store law independent of the public
scheduler.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Canonical normalized execution for a fixed amount of remaining fuel,
projected to the scheduling-insensitive semantic state. -/
def canonicalSemanticLaw (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) (fuel : Nat) (config : graph.Config) :
    FinDist graph.SemanticKey :=
  (graph.runPlan
    (graph.policyPlan (graph.normalizeProfile profile) graph.canonicalScheduler)
    fuel config).map graph.semanticKey

/-- A canonical normalized continuation depends only on the semantic key, for
every fuel bound. -/
theorem canonicalSemanticLaw_congr (profile : graph.BehavioralProfile) :
    ∀ fuel {left right : graph.Config},
      graph.semanticKey left = graph.semanticKey right →
        graph.canonicalSemanticLaw profile fuel left =
          graph.canonicalSemanticLaw profile fuel right := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right same
      simpa [canonicalSemanticLaw, runPlan] using congrArg FinDist.pure same
  | succ fuel ih =>
      intro left right same
      have cutEq := semanticKey_cut_eq same
      by_cases leftTerminal : left.cut.Terminal
      · have rightTerminal : right.cut.Terminal := by
          rw [← cutEq]
          exact leftTerminal
        simp [canonicalSemanticLaw, runPlan, leftTerminal, rightTerminal, same]
      · have rightTerminal : ¬ right.cut.Terminal := by
          rw [← cutEq]
          exact leftTerminal
        let event := left.cut.enabled.min'
          (enabled_nonempty_of_not_terminal left leftTerminal)
        have leftReady : left.cut.Ready event :=
          (EventOrder.Cut.mem_enabled _ _).mp
            (Finset.min'_mem _ (enabled_nonempty_of_not_terminal left leftTerminal))
        have least : ∀ other, other ∉ left.cut.completed → event.val ≤ other.val := by
          intro other unfinished
          exact (canonical_min_ready_is_least_unfinished left.cut leftTerminal).2
            other unfinished
        have rightReady : right.cut.Ready event := by
          rw [← cutEq]
          exact leftReady
        have rightLeast : ∀ other, other ∉ right.cut.completed →
            event.val ≤ other.val := by
          intro other unfinished
          apply least other
          rwa [cutEq]
        rw [canonicalSemanticLaw, canonicalSemanticLaw,
          runPlan_canonical_normalized_step profile fuel left event leftReady least,
          runPlan_canonical_normalized_step profile fuel right event rightReady rightLeast,
          FinDist.map_bind, FinDist.map_bind]
        apply bind_eq_of_semanticKey_map_eq
          (graph.normalizedPolicyStep profile left event leftReady)
          (graph.normalizedPolicyStep profile right event rightReady)
        · exact graph.normalizedPolicyStep_map_semanticKey_congr profile same event
            leftReady rightReady
        · intro leftNext _ rightNext _ nextSame
          exact ih nextSame

/-- Run the canonical normalized continuation with exactly the number of
unfinished events. -/
def canonicalContinuation (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) (config : graph.Config) :
    FinDist graph.SemanticKey :=
  graph.canonicalSemanticLaw profile config.remaining config

/-- At the empty cut the continuation is the complete canonical execution
law, including the original-action recall retained in the semantic key. -/
theorem canonicalContinuation_initial (profile : graph.BehavioralProfile)
    (inputs : graph.Inputs) :
    graph.canonicalContinuation profile (Config.initial inputs) =
      (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile)
        inputs).map graph.semanticKey := by
  have remaining : (Config.initial inputs : graph.Config).remaining =
      graph.order.eventCount := by
    simp [Config.remaining, Config.initial, EventOrder.Cut.empty]
  simp only [canonicalContinuation, remaining, canonicalSemanticLaw,
    runPolicies, EventGraph.run]

/-- Exact-fuel canonical continuations also factor through semantic state. -/
theorem canonicalContinuation_congr (profile : graph.BehavioralProfile)
    {left right : graph.Config}
    (same : graph.semanticKey left = graph.semanticKey right) :
    graph.canonicalContinuation profile left =
      graph.canonicalContinuation profile right := by
  have cutEq := semanticKey_cut_eq same
  have remainingEq : left.remaining = right.remaining := by
    unfold Config.remaining
    rw [cutEq]
  unfold canonicalContinuation
  rw [remainingEq]
  exact canonicalSemanticLaw_congr profile right.remaining same

/-- Execute one chosen normalized event and then use canonical scheduling. -/
def normalizedThenCanonical (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) :
    FinDist graph.SemanticKey :=
  (graph.normalizedPolicyStep profile config event ready).bind
    (graph.canonicalContinuation profile)

/-- The canonical continuation exposes any ready event that is least among
unfinished events as its first normalized step. -/
theorem canonicalContinuation_step (profile : graph.BehavioralProfile)
    (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val) :
    graph.canonicalContinuation profile config =
      graph.normalizedThenCanonical profile config event ready := by
  have positive : 0 < config.remaining := by
    have notTerminal : ¬ config.cut.Terminal := by
      intro terminal
      exact ready.1 (by rw [terminal]; simp)
    have nonzero : config.remaining ≠ 0 := by
      intro zero
      exact notTerminal (config.terminal_iff_remaining_zero.mpr zero)
    omega
  obtain ⟨fuel, remainingEq⟩ : ∃ fuel, config.remaining = fuel + 1 := by
    exact ⟨config.remaining - 1, by omega⟩
  unfold canonicalContinuation canonicalSemanticLaw normalizedThenCanonical
  rw [remainingEq, runPlan_canonical_normalized_step profile fuel config event ready least,
    FinDist.map_bind]
  apply FinDist.bind_congr
  intro next member
  have decreased := graph.normalizedPolicyStep_remaining profile config event ready next member
  have nextRemaining : next.remaining = fuel := by omega
  change _ = graph.canonicalSemanticLaw profile next.remaining next
  rw [nextRemaining]
  rfl

private theorem normalizedThenCanonical_insert_second
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstOwner secondOwner : Player)
    (firstActor : graph.actor? first = some firstOwner)
    (secondActor : graph.actor? second = some secondOwner)
    (insertSecond : ∀ (firstAction : graph.Action first) next
      (member : next ∈ (config.step first firstReady firstAction).support),
      let nextReady : next.cut.Ready second := by
        rw [config.step_cut first firstReady firstAction next member]
        exact secondReady.after_complete firstReady different.symm
      graph.normalizedThenCanonical profile next second nextReady =
        graph.canonicalContinuation profile next) :
    graph.normalizedThenCanonical profile config first firstReady =
      (policyStepThen profile config first second firstReady secondReady different
        firstOwner secondOwner firstActor secondActor).bind
          (graph.canonicalContinuation profile) := by
  unfold normalizedThenCanonical policyStepThen
  unfold normalizedPolicyStep
  split
  · rename_i owner actor
    have ownerEq : owner = firstOwner := Option.some.inj (actor.symm.trans firstActor)
    subst owner
    simp only [FinDist.bind_bind]
    apply FinDist.bind_congr
    intro firstAction _
    rw [← FinDist.bindOnSupport_eq_bind
      (config.step first firstReady firstAction) (graph.canonicalContinuation profile)]
    rw [FinDist.bind_bindOnSupport]
    apply FinDist.bindOnSupport_congr
    intro next member
    have nextReady : next.cut.Ready second := by
      rw [config.step_cut first firstReady firstAction next member]
      exact secondReady.after_complete firstReady different.symm
    have recur := insertSecond firstAction next member
    change graph.normalizedThenCanonical profile next second nextReady =
      graph.canonicalContinuation profile next at recur
    have secondStepEq :
        graph.normalizedPolicyStep profile next second nextReady =
          (graph.normalizePolicy secondOwner (profile secondOwner) second secondActor
            (graph.playerObserve secondOwner next)).bind
              (next.step second nextReady) := by
      unfold normalizedPolicyStep
      split
      · rename_i owner actor
        have ownerEq : owner = secondOwner :=
          Option.some.inj (actor.symm.trans secondActor)
        subst owner
        rfl
      · rename_i ownerless
        simp [ownerless] at secondActor
    rw [← recur]
    unfold normalizedThenCanonical
    rw [secondStepEq, FinDist.bind_bind]
  · rename_i ownerless
    simp [ownerless] at firstActor

/-- Local confluence: choosing any ready event and then reverting to canonical
scheduling has exactly the canonical semantic-state law. -/
theorem BarrierOrdered.normalizedThenCanonical_eq
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) :
    graph.normalizedThenCanonical profile config event ready =
      graph.canonicalContinuation profile config := by
  generalize remainingEq : config.remaining = remaining
  induction remaining using Nat.strong_induction_on generalizing config event with
  | h remaining ih =>
      have notTerminal : ¬ config.cut.Terminal := by
        intro terminal
        exact ready.1 (by rw [terminal]; simp)
      let canonical := config.cut.enabled.min'
        (enabled_nonempty_of_not_terminal config notTerminal)
      have canonicalReady : config.cut.Ready canonical :=
        (EventOrder.Cut.mem_enabled _ _).mp
          (Finset.min'_mem _ (enabled_nonempty_of_not_terminal config notTerminal))
      have least : ∀ other, other ∉ config.cut.completed →
          canonical.val ≤ other.val := by
        intro other unfinished
        exact (canonical_min_ready_is_least_unfinished config.cut notTerminal).2
          other unfinished
      by_cases same : event = canonical
      · subst event
        exact (canonicalContinuation_step profile config canonical canonicalReady least).symm
      · obtain ⟨eventOwner, canonicalOwner, eventActor, canonicalActor, ownerNe⟩ :=
          ordered.ready_pair_actors ready canonicalReady same
        let eventThenCanonical := policyStepThen profile config event canonical ready
          canonicalReady same eventOwner canonicalOwner eventActor canonicalActor
        let canonicalThenEvent := policyStepThen profile config canonical event
          canonicalReady ready (Ne.symm same) canonicalOwner eventOwner canonicalActor eventActor
        have insertCanonical : ∀ (eventAction : graph.Action event) next
            (member : next ∈ (config.step event ready eventAction).support),
            let nextReady : next.cut.Ready canonical := by
              rw [config.step_cut event ready eventAction next member]
              exact canonicalReady.after_complete ready (Ne.symm same)
            graph.normalizedThenCanonical profile next canonical nextReady =
              graph.canonicalContinuation profile next := by
          intro eventAction next member
          have decreased := config.remaining_step event ready eventAction next member
          apply ih next.remaining
          · omega
          · rfl
        have insertEvent : ∀ (canonicalAction : graph.Action canonical) next
            (member : next ∈
              (config.step canonical canonicalReady canonicalAction).support),
            let nextReady : next.cut.Ready event := by
              rw [config.step_cut canonical canonicalReady canonicalAction next member]
              exact ready.after_complete canonicalReady same
            graph.normalizedThenCanonical profile next event nextReady =
              graph.canonicalContinuation profile next := by
          intro canonicalAction next member
          have decreased := config.remaining_step canonical canonicalReady
            canonicalAction next member
          apply ih next.remaining
          · omega
          · rfl
        have firstExpansion :
            graph.normalizedThenCanonical profile config event ready =
              eventThenCanonical.bind (graph.canonicalContinuation profile) := by
          exact normalizedThenCanonical_insert_second profile config event canonical
            ready canonicalReady same eventOwner canonicalOwner eventActor canonicalActor
            insertCanonical
        have canonicalExpansion :
            graph.normalizedThenCanonical profile config canonical canonicalReady =
              canonicalThenEvent.bind (graph.canonicalContinuation profile) := by
          exact normalizedThenCanonical_insert_second profile config canonical event
            canonicalReady ready (Ne.symm same) canonicalOwner eventOwner canonicalActor eventActor
            insertEvent
        have diamond : eventThenCanonical.map graph.semanticKey =
            canonicalThenEvent.map graph.semanticKey := by
          exact ordered.policyStepThen_map_semanticKey_comm profile config event canonical
            ready canonicalReady same eventOwner canonicalOwner eventActor canonicalActor
        have continuationEq :
            eventThenCanonical.bind (graph.canonicalContinuation profile) =
              canonicalThenEvent.bind (graph.canonicalContinuation profile) := by
          apply bind_eq_of_semanticKey_map_eq eventThenCanonical canonicalThenEvent diamond
          intro left _ right _ keyEq
          exact canonicalContinuation_congr profile keyEq
        calc
          graph.normalizedThenCanonical profile config event ready =
              eventThenCanonical.bind (graph.canonicalContinuation profile) := firstExpansion
          _ = canonicalThenEvent.bind (graph.canonicalContinuation profile) := continuationEq
          _ = graph.normalizedThenCanonical profile config canonical canonicalReady :=
            canonicalExpansion.symm
          _ = graph.canonicalContinuation profile config :=
            (canonicalContinuation_step profile config canonical canonicalReady least).symm

/-- At a terminal cut the canonical continuation is the point mass at the
current semantic state. -/
theorem canonicalContinuation_terminal (profile : graph.BehavioralProfile)
    (config : graph.Config) (terminal : config.cut.Terminal) :
    FinDist.pure (graph.semanticKey config) =
      graph.canonicalContinuation profile config := by
  have remainingZero := config.terminal_iff_remaining_zero.mp terminal
  simp [canonicalContinuation, canonicalSemanticLaw, remainingZero, runPlan]

/-- The actual normalized runner under any adaptive public scheduler has the
canonical semantic continuation law once fuel covers the unfinished events. -/
theorem BarrierOrdered.runPlan_normalized_semantic_eq_canonical
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) (fuel : Nat) (config : graph.Config)
    (enough : config.remaining ≤ fuel) :
    (graph.runPlan
      (graph.policyPlan (graph.normalizeProfile profile) scheduler)
      fuel config).map graph.semanticKey =
        graph.canonicalContinuation profile config := by
  apply runPlan_map_eq_value_of_step
    (graph.policyPlan (graph.normalizeProfile profile) scheduler)
    graph.semanticKey (graph.canonicalContinuation profile)
    (canonicalContinuation_terminal profile)
  · intro current notTerminal
    unfold policyPlan
    rw [FinDist.bind_bind]
    calc
      _ = (scheduler (graph.publicObserve current) current.cut.enabled
          (enabled_nonempty_of_not_terminal current notTerminal)).bind
            (fun _ => graph.canonicalContinuation profile current) := by
        apply FinDist.bind_congr
        intro selected _
        have ready : current.cut.Ready selected.1 :=
          (EventOrder.Cut.mem_enabled _ _).mp selected.2
        have localLaw := ordered.normalizedThenCanonical_eq profile current selected.1 ready
        split
        · rename_i owner actor
          rw [FinDist.bind_map]
          unfold normalizedThenCanonical normalizedPolicyStep at localLaw
          split at localLaw
          · rename_i actualOwner actualActor
            have ownerEq : actualOwner = owner :=
              Option.some.inj (actualActor.symm.trans actor)
            subst actualOwner
            simpa [normalizeProfile, normalizePolicy, FinDist.bind_bind] using localLaw
          · rename_i ownerless
            simp [ownerless] at actor
        · rename_i ownerless
          rw [FinDist.pure_bind]
          unfold normalizedThenCanonical normalizedPolicyStep at localLaw
          split at localLaw
          · rename_i owner actor
            simp [ownerless] at actor
          · simpa using localLaw
      _ = graph.canonicalContinuation profile current := FinDist.bind_const _ _
  · exact enough

/-- Full honest scheduling law: after normalizing completion-order metadata in
every player policy, any adaptive public scheduler has the same terminal typed
store law as the canonical scheduler. -/
theorem BarrierOrdered.runPolicies_store_eq_canonical
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) (inputs : graph.Inputs) :
    (graph.runPolicies scheduler (graph.normalizeProfile profile) inputs).map
        Config.store =
      (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) inputs).map
        Config.store := by
  have enough : (Config.initial inputs : graph.Config).remaining ≤
      graph.order.eventCount := by
    simp [Config.remaining, Config.initial]
  have semanticEq := ordered.runPlan_normalized_semantic_eq_canonical profile scheduler
    graph.order.eventCount (Config.initial inputs) enough
  have initialRemaining : (Config.initial inputs : graph.Config).remaining =
      graph.order.eventCount := by
    simp [Config.remaining, Config.initial, EventOrder.Cut.empty]
  unfold canonicalContinuation at semanticEq
  rw [initialRemaining] at semanticEq
  have keyEq :
      (graph.runPolicies scheduler (graph.normalizeProfile profile) inputs).map
          graph.semanticKey =
        (graph.runPolicies graph.canonicalScheduler
          (graph.normalizeProfile profile) inputs).map graph.semanticKey := by
    simpa [runPolicies, EventGraph.run, canonicalSemanticLaw] using semanticEq
  have projected := congrArg
    (fun law : FinDist graph.SemanticKey => law.map fun key => key.2.1) keyEq
  simpa [FinDist.map_comp, semanticKey, storeRecall, Function.comp_def] using projected

end Vegas.EventGraph
