/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Semantics

/-! # The public scheduler that serves one player last

Among the enabled events, the scheduler takes the least event not owned by a
given player, and an event of that player only when every enabled event is
its own. It reads only the enabled set and public actors, so it is a public
scheduler. When that player is scheduled, everything other players could do
first has been done.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]

/-- The enabled events not owned by `who`. -/
def othersEnabled (graph : Vegas.EventGraph Player L) (who : Player)
    (enabled : Finset graph.EventId) : Finset graph.EventId :=
  enabled.filter fun event => graph.actor? event ≠ some who

/-- The event served first when `who` is served last: the least enabled event
of another owner or of chance, and the least enabled event otherwise. -/
def lastPick (graph : Vegas.EventGraph Player L) (who : Player) (enabled : Finset graph.EventId)
    (nonempty : enabled.Nonempty) : graph.EventId :=
  if others : (graph.othersEnabled who enabled).Nonempty then
    (graph.othersEnabled who enabled).min' others
  else enabled.min' nonempty

theorem lastPick_mem (graph : Vegas.EventGraph Player L) (who : Player)
    (enabled : Finset graph.EventId) (nonempty : enabled.Nonempty) :
    graph.lastPick who enabled nonempty ∈ enabled := by
  unfold lastPick
  split
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
  · exact Finset.min'_mem _ _

/-- The pick depends only on the enabled set. -/
theorem lastPick_congr (graph : Vegas.EventGraph Player L) (who : Player)
    {left right : Finset graph.EventId} (same : left = right) (leftNonempty : left.Nonempty)
    (rightNonempty : right.Nonempty) :
    graph.lastPick who left leftNonempty = graph.lastPick who right rightNonempty := by
  subst same
  rfl

/-- When another player's or a chance event is enabled, the pick is not an
event of `who`. -/
theorem lastPick_other (graph : Vegas.EventGraph Player L) (who : Player)
    {enabled : Finset graph.EventId} (nonempty : enabled.Nonempty) {event : graph.EventId}
    (member : event ∈ enabled) (foreign : graph.actor? event ≠ some who) :
    graph.actor? (graph.lastPick who enabled nonempty) ≠ some who := by
  have others : (graph.othersEnabled who enabled).Nonempty :=
    ⟨event, Finset.mem_filter.mpr ⟨member, foreign⟩⟩
  unfold lastPick
  rw [dite_eq_left others]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ others)).2

/-- **The scheduler that serves `who` last.** -/
def lastScheduler (graph : Vegas.EventGraph Player L) (who : Player) : PublicScheduler graph :=
  fun _ enabled nonempty =>
    PMF.pure ⟨graph.lastPick who enabled nonempty, graph.lastPick_mem who enabled nonempty⟩

/-- When the last scheduler selects an event of `who`, every enabled event is
an event of `who`. -/
theorem lastScheduler_selects_owned (graph : Vegas.EventGraph Player L) (who : Player)
    (observation : graph.PublicObservation) (enabled : Finset graph.EventId)
    (nonempty : enabled.Nonempty) (selected : {event : graph.EventId // event ∈ enabled})
    (member : selected ∈ (graph.lastScheduler who observation enabled nonempty).support)
    (owned : graph.actor? selected.1 = some who) :
    ∀ other ∈ enabled, graph.actor? other = some who := by
  intro other enabledOther
  by_contra foreign
  unfold lastScheduler at member
  rw [PMF.mem_support_pure_iff] at member
  rw [member] at owned
  exact graph.lastPick_other who nonempty enabledOther foreign owned

end Vegas.EventGraph
