module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Semantics
public import Vegas.EventGraph.Sequential
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

/-! # Canonical step equations

Source-order simulation uses the ordinary graph runner. At a completed numeric
prefix its canonical scheduler selects the next rank; the following equations
expose the actual player and chance kernels of that runner.
-/

noncomputable section

namespace Vegas.EventOrder.Cut

variable {order : EventOrder}

/-- Exactly the first `length` ranked events have completed. -/
def IsPrefix (cut : order.Cut) (length : Nat) : Prop :=
  length ≤ order.eventCount ∧ ∀ event, event ∈ cut.completed ↔ event.val < length

theorem empty_isPrefix (order : EventOrder) : (empty order).IsPrefix 0 := by
  simp [IsPrefix, empty]

/-- A completed cut determines its numeric prefix length uniquely. -/
theorem IsPrefix.unique {cut : order.Cut} {first second : Nat}
    (left : cut.IsPrefix first) (right : cut.IsPrefix second) : first = second := by
  by_contra different
  rcases Nat.lt_or_gt_of_ne different with lower | upper
  · have inside : first < order.eventCount := by have := right.1; omega
    have completed := (right.2 ⟨first, inside⟩).mpr lower
    exact Nat.lt_irrefl _ ((left.2 ⟨first, inside⟩).mp completed)
  · have inside : second < order.eventCount := by have := left.1; omega
    have completed := (left.2 ⟨second, inside⟩).mpr upper
    exact Nat.lt_irrefl _ ((right.2 ⟨second, inside⟩).mp completed)

/-- A numeric prefix contains exactly its stated number of events. -/
theorem IsPrefix.card {cut : order.Cut} {length : Nat}
    (ordered : cut.IsPrefix length) : cut.completed.card = length := by
  by_cases active : length < order.eventCount
  · have same : cut.completed = Finset.Iio (⟨length, active⟩ : Fin order.eventCount) := by
      ext event
      exact (ordered.2 event).trans (by simp only [Finset.mem_Iio]; rfl)
    rw [same, Fin.card_Iio]
  · have lengthEq : length = order.eventCount := by have := ordered.1; omega
    have same : cut.completed = Finset.univ := by
      ext event
      simp only [Finset.mem_univ, iff_true]
      exact (ordered.2 event).mpr (lengthEq ▸ event.isLt)
    rw [same, Finset.card_univ, Fintype.card_fin, lengthEq]

/-- The next numeric event is ready at a nonterminal prefix, irrespective of
which subset of earlier events is a direct dependency. -/
theorem IsPrefix.ready {cut : order.Cut} {length : Nat}
    (ordered : cut.IsPrefix length) (active : length < order.eventCount) :
    cut.Ready ⟨length, active⟩ := by
  constructor
  · rw [ordered.2]
    exact Nat.lt_irrefl _
  · intro event predecessor
    exact (ordered.2 event).mpr (order.predecessor_lt predecessor)

/-- Completing the next event extends the prefix by exactly one. -/
theorem IsPrefix.complete {cut : order.Cut} {length : Nat}
    (ordered : cut.IsPrefix length) (active : length < order.eventCount) :
    (cut.complete ⟨length, active⟩ (ordered.ready active)).IsPrefix (length + 1) := by
  refine ⟨by omega, ?_⟩
  intro event
  rw [mem_complete, ordered.2]
  simp only [Fin.ext_iff]
  omega

/-- The prefix update also applies when the next rank is named through a
typed event embedding rather than a literal numeric event. -/
theorem IsPrefix.complete_at {cut : order.Cut} {length : Nat}
    (ordered : cut.IsPrefix length) (event : Fin order.eventCount)
    (ready : cut.Ready event) (rank : event.val = length) :
    (cut.complete event ready).IsPrefix (length + 1) := by
  have active : length < order.eventCount := rank ▸ event.isLt
  have same : event = ⟨length, active⟩ := Fin.ext rank
  subst event
  exact ordered.complete active

theorem IsPrefix.terminal {cut : order.Cut}
    (ordered : cut.IsPrefix order.eventCount) : cut.Terminal := by
  apply Finset.ext
  intro event
  simp [ordered.2 event, event.isLt]

end Vegas.EventOrder.Cut

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- A ready event that precedes every unfinished event is the canonical
scheduler's actual choice. -/
theorem canonical_selected_eq (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val) :
    config.cut.enabled.min' (enabled_nonempty_of_not_terminal config
      ready.not_terminal) = event := by
  apply le_antisymm
  · exact Finset.min'_le _ _ ((EventOrder.Cut.mem_enabled _ _).mpr ready)
  · apply least
    exact ((EventOrder.Cut.mem_enabled _ _).mp (Finset.min'_mem _ _)).1

omit [DecidableEq Player] in
private theorem canonicalScheduler_eq_pure (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val) :
    graph.canonicalScheduler (graph.publicObserve config) config.cut.enabled
        (enabled_nonempty_of_not_terminal config ready.not_terminal) =
      PMF.pure ⟨event, (EventOrder.Cut.mem_enabled _ _).mpr ready⟩ := by
  apply congrArg PMF.pure
  apply Subtype.ext
  exact canonical_selected_eq config event ready least

/-- A canonical owned event uses the active callback or mechanical failure,
according to the public default status of its owner. -/
theorem runPlan_canonical_actor_cases (profile : graph.BehavioralProfile)
    (fuel : Nat) (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val)
    (who : Player) (actor : graph.actor? event = some who) :
    graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (fuel + 1) config =
      (if inactive : who ∈ config.defaulted then
        PMF.pure ((graph.nodes event).failureAction who actor)
      else profile who event actor (graph.playerObserve who config) inactive).bind fun action =>
        (config.step event ready action).bind
          (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) fuel) := by
  rw [runPlan_policyPlan_succ profile _ fuel config ready.not_terminal,
    canonicalScheduler_eq_pure config event ready least, PMF.pure_bind, eventStep,
    actionLaw_of_actor profile config actor, PMF.bind_bind]

/-- At an active canonical owned event, the shared executor runs the actual
observation-local callback and then that event's semantic step. -/
theorem runPlan_canonical_actor (profile : graph.BehavioralProfile)
    (fuel : Nat) (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val)
    (who : Player) (actor : graph.actor? event = some who)
    (active : who ∉ config.defaulted) :
    graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (fuel + 1) config =
      (profile who event actor (graph.playerObserve who config) active).bind fun action =>
        (config.step event ready action).bind
          (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) fuel) := by
  rw [runPlan_canonical_actor_cases profile fuel config event ready least who actor,
    dite_eq_right active]

/-- A defaulted owner's canonical event calls no player policy. The executor
suppresses every requested action, so any supplied action names the same step. -/
theorem runPlan_canonical_defaulted (profile : graph.BehavioralProfile)
    (fuel : Nat) (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val)
    (who : Player) (actor : graph.actor? event = some who)
    (inactive : who ∈ config.defaulted) (action : graph.Action event) :
    graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (fuel + 1) config =
      (config.step event ready action).bind
        (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) fuel) := by
  rw [runPlan_canonical_actor_cases profile fuel config event ready least who actor,
    dite_eq_left inactive, PMF.pure_bind]
  rw [config.step_eq_of_defaulted event ready who actor inactive
    ((graph.nodes event).failureAction who actor) action]

/-- A canonical sample step executes its retained chance kernel directly; no
player supplies that node's randomness. -/
theorem runPlan_canonical_ownerless (profile : graph.BehavioralProfile)
    (fuel : Nat) (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val)
    (ownerless : graph.actor? event = none) :
    graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (fuel + 1) config =
      (config.step event ready
        (EventCode.actionOfActorNone (graph.nodes event) ownerless)).bind
          (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) fuel) := by
  rw [runPlan_policyPlan_succ profile _ fuel config ready.not_terminal,
    canonicalScheduler_eq_pure config event ready least, PMF.pure_bind, eventStep,
    actionLaw_of_ownerless profile config ownerless, PMF.pure_bind]

/-- A bounded canonical run advances its completed source prefix by its execution count. -/
theorem runPlan_canonical_isPrefix
    (profile : graph.BehavioralProfile) :
    ∀ (count start : Nat) (origin : graph.Config), origin.cut.IsPrefix start →
      start + count ≤ graph.order.eventCount →
      ∀ final ∈ (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
        count origin).support, final.cut.IsPrefix (start + count) := by
  intro count
  induction count with
  | zero =>
      intro start origin ordered _bounded final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      simpa only [Nat.add_zero] using ordered
  | succ count ih =>
      intro start origin ordered bounded final reached
      have active : start < graph.order.eventCount := by omega
      let event : graph.EventId := ⟨start, active⟩
      have ready : origin.cut.Ready event := ordered.ready active
      have least : ∀ other, other ∉ origin.cut.completed → event.val ≤ other.val := by
        intro other unfinished
        have notBefore : ¬ other.val < start := by
          simpa only [ordered.2 other] using unfinished
        exact Nat.le_of_not_gt notBefore
      have tails (action : graph.Action event) (next : graph.Config)
          (selected : next ∈ (origin.step event ready action).support)
          (rest : final ∈ (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
            count next).support) : final.cut.IsPrefix (start + (count + 1)) := by
        have nextPrefix : next.cut.IsPrefix (start + 1) := by
          rw [origin.step_cut event ready action next selected]
          exact ordered.complete active
        have result := ih (start + 1) next nextPrefix (by omega) final rest
        rwa [show start + 1 + count = start + (count + 1) by omega] at result
      cases actor : graph.actor? event with
      | none =>
          rw [runPlan_canonical_ownerless profile count origin event ready least actor] at reached
          obtain ⟨next, selected, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
          exact tails _ next selected rest
      | some who =>
          by_cases inactive : who ∈ origin.defaulted
          · rw [runPlan_canonical_defaulted profile count origin event ready least who actor
              inactive ((graph.nodes event).failureAction who actor)] at reached
            obtain ⟨next, selected, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
            exact tails _ next selected rest
          · rw [runPlan_canonical_actor profile count origin event ready least who actor inactive]
              at reached
            obtain ⟨action, _selected, remainder⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
            obtain ⟨next, selected, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp remainder
            exact tails action next selected rest


end Vegas.EventGraph

namespace Vegas.EventGraph.Config.Step

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A finite path of the sequential executor extends its numeric completed
prefix, possibly by more than one event. -/
theorem path_isPrefix_sequential (graph : Vegas.EventGraph Player L)
    {before after : graph.sequentialize.Config}
    (path : Relation.ReflTransGen Config.Step before after)
    {rank : Nat} (ordered : before.cut.IsPrefix rank) :
    ∃ nextRank, rank ≤ nextRank ∧ after.cut.IsPrefix nextRank := by
  induction path using Relation.ReflTransGen.head_induction_on generalizing rank with
  | refl => exact ⟨rank, le_rfl, ordered⟩
  | @head before middle moved _ ih =>
      obtain ⟨event, ready, action, supported⟩ := moved
      have actual : before.cut.IsPrefix event.val :=
        ⟨event.isLt.le, fun query =>
          graph.sequentialize_mem_completed_iff_lt_of_ready before.cut ready⟩
      have rankEq : event.val = rank := actual.unique ordered
      have nextPrefix : middle.cut.IsPrefix (rank + 1) := by
        rw [before.step_cut event ready action middle supported]
        exact ordered.complete_at event ready rankEq
      obtain ⟨nextRank, lower, finalPrefix⟩ := ih nextPrefix
      exact ⟨nextRank, by omega, finalPrefix⟩

/-- Every intermediate source rank occurs on a sequential graph path. -/
theorem path_prefix_at {graph : Vegas.EventGraph Player L}
    {first last : graph.sequentialize.Config}
    (path : Relation.ReflTransGen Config.Step first last) {start finish rank : Nat}
    (before : first.cut.IsPrefix start) (after : last.cut.IsPrefix finish)
    (lower : start ≤ rank) (upper : rank ≤ finish) :
    ∃ middle : graph.sequentialize.Config, middle.cut.IsPrefix rank ∧
      Relation.ReflTransGen Config.Step first middle ∧
      Relation.ReflTransGen Config.Step middle last := by
  induction path using Relation.ReflTransGen.head_induction_on generalizing start with
  | refl =>
      have same := before.unique after
      have atRank : start = rank := by omega
      exact ⟨_, atRank ▸ before, .refl, .refl⟩
  | @head first middle moved rest ih =>
      by_cases atRank : start = rank
      · exact ⟨first, atRank ▸ before, .refl, rest.head moved⟩
      obtain ⟨event, ready, action, supported⟩ := moved
      have actual : first.cut.IsPrefix event.val :=
        ⟨event.isLt.le, fun query =>
          graph.sequentialize_mem_completed_iff_lt_of_ready first.cut ready⟩
      have rankEq := actual.unique before
      have nextPrefix : middle.cut.IsPrefix (start + 1) := by
        rw [first.step_cut event ready action middle supported]
        exact before.complete_at event ready rankEq
      obtain ⟨found, ordered, prefixPath, suffixPath⟩ := ih nextPrefix (by omega)
      exact ⟨found, ordered, prefixPath.head ⟨event, ready, action, supported⟩, suffixPath⟩

end Vegas.EventGraph.Config.Step

namespace Vegas.EventGraph.Config

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

/-- A configuration's chronological history has one completion per completed
event, so at a prefix its length is the prefix rank. -/
theorem history_length_of_isPrefix {graph : Vegas.EventGraph Player L} (config : graph.Config)
    {rank : Nat} (ordered : config.cut.IsPrefix rank) : config.history.length = rank := by
  classical
  have completed : (config.history.map EventCompletion.event).toFinset =
      config.cut.completed := by
    ext event
    rw [List.mem_toFinset]
    exact config.history_exact event
  have filtered : config.cut.completed =
      (Finset.univ : Finset graph.EventId).filter fun event => event.val < rank := by
    ext event
    rw [Finset.mem_filter]
    exact ⟨fun member => ⟨Finset.mem_univ _, (ordered.2 event).mp member⟩,
      fun below => (ordered.2 event).mpr below.2⟩
  rw [← List.length_map (f := EventCompletion.event),
    ← List.toFinset_card_of_nodup config.history_nodup, completed, filtered]
  rw [show ((Finset.univ : Finset graph.EventId).filter fun event => event.val < rank) =
      Finset.univ.filter (fun event : Fin graph.order.eventCount => (event : Nat) < rank) from rfl,
    Fin.card_filter_val_lt]
  exact min_eq_right ordered.1

end Vegas.EventGraph.Config
