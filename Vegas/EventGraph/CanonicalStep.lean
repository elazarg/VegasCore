/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Semantics

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
private theorem not_terminal_of_ready (config : graph.Config) {event : graph.EventId}
    (ready : config.cut.Ready event) : ¬ config.cut.Terminal := by
  intro terminal
  exact ready.1 (terminal.symm ▸ Finset.mem_univ event)

omit [DecidableEq Player] in
/-- A ready event that precedes every unfinished event is the canonical
scheduler's actual choice. -/
theorem canonical_selected_eq (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val) :
    config.cut.enabled.min' (enabled_nonempty_of_not_terminal config
      (not_terminal_of_ready config ready)) = event := by
  apply le_antisymm
  · exact Finset.min'_le _ _ ((EventOrder.Cut.mem_enabled _ _).mpr ready)
  · apply least
    exact ((EventOrder.Cut.mem_enabled _ _).mp (Finset.min'_mem _ _)).1

omit [DecidableEq Player] in
private theorem canonicalScheduler_eq_pure (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val) :
    graph.canonicalScheduler (graph.publicObserve config) config.cut.enabled
        (enabled_nonempty_of_not_terminal config (not_terminal_of_ready config ready)) =
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
  rw [runPlan, dite_eq_right (not_terminal_of_ready config ready)]
  conv_lhs =>
    arg 1
    unfold policyPlan
    dsimp only
    rw [canonicalScheduler_eq_pure config event ready least, PMF.pure_bind]
  split
  · rename_i selectedOwner selectedActor
    have same : selectedOwner = who := Option.some.inj (selectedActor.symm.trans actor)
    subst selectedOwner
    by_cases inactive : who ∈ config.defaulted
    · simp only [dite_eq_left inactive, PMF.pure_bind]
    · simp only [dite_eq_right inactive, PMF.bind_map, Function.comp_def]
  · rename_i selectedActor
    have impossible : (none : Option Player) = some who := selectedActor.symm.trans actor
    cases impossible

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
  rw [runPlan, dite_eq_right (not_terminal_of_ready config ready)]
  conv_lhs =>
    arg 1
    unfold policyPlan
    dsimp only
    rw [canonicalScheduler_eq_pure config event ready least, PMF.pure_bind]
  split
  · rename_i selectedOwner selectedActor
    have impossible : (some selectedOwner : Option Player) = none :=
      selectedActor.symm.trans ownerless
    cases impossible
  · rw [PMF.pure_bind]

end Vegas.EventGraph
