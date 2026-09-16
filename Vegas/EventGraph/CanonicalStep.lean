/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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
      FinDist.pure ⟨event, (EventOrder.Cut.mem_enabled _ _).mpr ready⟩ := by
  apply congrArg FinDist.pure
  apply Subtype.ext
  exact canonical_selected_eq config event ready least

/-- At a strategic canonical step, the shared executor runs precisely the
actor's observation-local kernel and then the selected event's semantic step. -/
theorem runPlan_canonical_actor (profile : graph.BehavioralProfile)
    (fuel : Nat) (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val)
    (who : Player) (actor : graph.actor? event = some who) :
    graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (fuel + 1) config =
      (profile who event actor (graph.playerObserve who config)).bind fun action =>
        (config.step event ready action).bind
          (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) fuel) := by
  rw [runPlan, dif_neg (not_terminal_of_ready config ready)]
  conv_lhs =>
    arg 1
    unfold policyPlan
    dsimp only
    rw [canonicalScheduler_eq_pure config event ready least, FinDist.pure_bind]
  split
  · rename_i selectedOwner selectedActor
    have same : selectedOwner = who := Option.some.inj (selectedActor.symm.trans actor)
    subst selectedOwner
    rw [FinDist.bind_map]
  · rename_i selectedActor
    simp [actor] at selectedActor

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
  rw [runPlan, dif_neg (not_terminal_of_ready config ready)]
  conv_lhs =>
    arg 1
    unfold policyPlan
    dsimp only
    rw [canonicalScheduler_eq_pure config event ready least, FinDist.pure_bind]
  split
  · rename_i selectedOwner selectedActor
    simp [ownerless] at selectedActor
  · rw [FinDist.pure_bind]

end Vegas.EventGraph
