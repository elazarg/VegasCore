/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Barriers
import Mathlib.Data.List.Sort

/-! # Logical observations under public-barrier dependencies

The compiler's dependency policy gives each ready strategic event exactly the
public values, own inputs, and own bindings from its source-ranked prefix. Other players'
hidden bindings can complete out of order; chronological scheduling metadata
remains visible separately.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- The graph contains the compiler's public-barrier dependency policy.
Additional source-ranked dependencies may serialize otherwise independent
events without changing the logical information available at a ready event. -/
def BarrierOrdered (graph : Vegas.EventGraph Player L) : Prop :=
  ∀ event,
    (barrierOrder graph.outputLayout).predecessors event ⊆ graph.order.predecessors event

omit [DecidableEq Player] R in
private theorem ordering_symm (left right : EventField Player L)
    (ordered : left.IsPublic ∨ right.IsPublic ∨ left.SameBindingOwner right) :
    right.IsPublic ∨ left.IsPublic ∨ right.SameBindingOwner left := by
  cases left <;> cases right <;>
    simp_all [EventField.IsPublic, EventField.SameBindingOwner]

omit [DecidableEq Player] in
private theorem visible_requires_order {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (who : Player)
    (actor : code.actor = some who) (other : EventField Player L)
    (otherCode : EventCode layout other)
    (visible : other.VisibleTo who) :
    other.IsPublic ∨ output.IsPublic ∨ other.SameBindingOwner output := by
  cases code with
  | bind owner payload =>
      simp only [EventCode.actor, Option.some.injEq] at actor
      subst owner
      cases otherCode <;>
        simp_all [EventField.IsPublic, EventField.VisibleTo, EventField.SameBindingOwner]
  | resolve => exact Or.inr (Or.inl trivial)
  | sample => simp [EventCode.actor] at actor

omit [DecidableEq Player] in
private theorem actor_output_visible {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (who : Player) (actor : code.actor = some who) :
    output.VisibleTo who := by
  cases code <;> simp_all [EventCode.actor, EventField.VisibleTo]

namespace BarrierOrdered

variable {graph : Vegas.EventGraph Player L}

/-- A ready public event is the unique ready event. Public events are genuine
barriers: they wait for the whole earlier prefix, and every later event waits
for them. -/
theorem ready_public_unique (ordered : graph.BarrierOrdered)
    (cut : graph.order.Cut) {event other : graph.EventId}
    (isPublic : (graph.outputLayout event).IsPublic)
    (ready : cut.Ready event) (otherReady : cut.Ready other) :
    other = event := by
  rcases lt_trichotomy other.val event.val with earlier | same | later
  · have predecessor : other ∈ graph.order.predecessors event := by
      exact ordered event
        (barrierOrder_public_event graph.outputLayout earlier isPublic)
    exact False.elim (otherReady.1 (ready.2 predecessor))
  · exact Fin.ext same
  · have predecessor : event ∈ graph.order.predecessors other := by
      exact ordered other
        (barrierOrder_public_prior graph.outputLayout later isPublic)
    exact False.elim (ready.1 (otherReady.2 predecessor))

/-- Every earlier output visible to a strategic actor is a direct dependency. -/
theorem visible_predecessor (ordered : graph.BarrierOrdered)
    {event other : graph.EventId} {who : Player}
    (actor : graph.actor? event = some who) (earlier : other.val < event.val)
    (visible : (graph.outputLayout other).VisibleTo who) :
    other ∈ graph.order.predecessors event := by
  apply ordered event
  exact (mem_barrierOrder graph.outputLayout other event).2
    ⟨earlier, visible_requires_order (graph.nodes event) who actor _ (graph.nodes other) visible⟩

/-- At a ready strategic event, each visible output is available precisely
when its producer is earlier in the source ranking. -/
theorem ready_visible_iff (ordered : graph.BarrierOrdered) (cut : graph.order.Cut)
    {event other : graph.EventId} {who : Player}
    (ready : cut.Ready event) (actor : graph.actor? event = some who)
    (visible : (graph.outputLayout other).VisibleTo who) :
    other ∈ cut.completed ↔ other.val < event.val := by
  constructor
  · intro completed
    by_contra notEarlier
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt notEarlier) with same | later
    · have eventEq : event = other := Fin.ext same
      exact ready.1 (eventEq ▸ completed)
    · have isPredecessor : event ∈ graph.order.predecessors other := by
        apply ordered other
        exact (mem_barrierOrder graph.outputLayout event other).2
          ⟨later, ordering_symm _ _
            (visible_requires_order (graph.nodes event) who actor _ (graph.nodes other) visible)⟩
      exact ready.1 (cut.predecessor_closed completed isPredecessor)
  · intro earlier
    exact ready.2 (ordered.visible_predecessor actor earlier visible)

end BarrierOrdered

/-- Initial fields and source-earlier event outputs visible to one player. -/
def prefixFields (graph : Vegas.EventGraph Player L) (who : Player)
    (event : graph.EventId) : Finset graph.Field := by
  classical
  exact Finset.univ.filter fun field => graph.fieldVisibleTo who field ∧
    match field with
    | .inl _ => True
    | .inr producer => producer.val < event.val

/-- The source-ranked logical decision schema used by the barrier compiler. -/
def prefixSchema (graph : Vegas.EventGraph Player L) : graph.LogicalSchema where
  fields event := match graph.actor? event with
    | none => ∅
    | some who => graph.prefixFields who event
  ownHistory event := match graph.actor? event with
    | none => []
    | some who => (List.finRange graph.order.eventCount).filter fun prior =>
        prior.val < event.val ∧ graph.actor? prior = some who

/-- Public-barrier dependencies certify the complete value and own-action
information available at every ready strategic event, for every completed cut.
The certificate does not erase or equate chronological scheduling metadata. -/
theorem BarrierOrdered.informationDiscipline {graph : Vegas.EventGraph Player L}
    (ordered : graph.BarrierOrdered) : graph.InformationDiscipline graph.prefixSchema where
  fields_visible := by
    intro event who actor field member
    simp only [prefixSchema, actor, prefixFields, Finset.mem_filter,
      Finset.mem_univ, true_and] at member
    exact member.1
  fields_causal := by
    intro event field member
    cases actor : graph.actor? event with
    | none => simp [prefixSchema, actor] at member
    | some who =>
        cases field with
        | inl => trivial
        | inr prior =>
            have member' := member
            simp only [prefixSchema, actor, prefixFields, Finset.mem_filter,
              Finset.mem_univ, true_and] at member'
            have facts : (graph.outputLayout prior).VisibleTo who ∧
                prior.val < event.val := ⟨by
              simpa [fieldVisibleTo, layout, fieldLayout] using member'.1, member'.2⟩
            exact ordered.visible_predecessor actor facts.2 facts.1
  ready_fields_exact := by
    intro cut event who ready actor
    ext field
    simp only [prefixSchema, actor, prefixFields, visibleFields, Finset.mem_filter,
      Finset.mem_univ, true_and]
    cases field with
    | inl => simp [FieldAvailable]
    | inr prior =>
        change (prior ∈ cut.completed ∧ (graph.outputLayout prior).VisibleTo who) ↔
          (graph.outputLayout prior).VisibleTo who ∧ prior.val < event.val
        constructor
        · rintro ⟨completed, visible⟩
          exact ⟨visible, (ordered.ready_visible_iff cut ready actor visible).mp completed⟩
        · rintro ⟨visible, earlier⟩
          exact ⟨(ordered.ready_visible_iff cut ready actor visible).mpr earlier, visible⟩
  own_history_ranked := by
    intro event
    cases actor : graph.actor? event with
    | none => simp [prefixSchema, actor]
    | some who =>
        simpa [prefixSchema, actor] using
          (List.sortedLT_finRange graph.order.eventCount).pairwise.filter
            (fun prior => decide (prior.val < event.val ∧ graph.actor? prior = some who))
  own_history_owned := by
    intro event who actor prior member
    have facts : prior.val < event.val ∧ graph.actor? prior = some who := by
      simpa [prefixSchema, actor] using member
    exact facts.2
  own_history_causal := by
    intro event prior member
    cases actor : graph.actor? event with
    | none => simp [prefixSchema, actor] at member
    | some who =>
        have facts : prior.val < event.val ∧ graph.actor? prior = some who := by
          simpa [prefixSchema, actor] using member
        exact ordered.visible_predecessor actor facts.1
          (actor_output_visible (graph.nodes prior) who facts.2)
  ready_own_history_exact := by
    intro cut event who ready actor
    ext prior
    simp only [prefixSchema, actor, List.mem_toFinset, List.mem_filter,
      List.mem_finRange, true_and, decide_eq_true_eq, completedOwnEvents,
      Finset.mem_filter]
    constructor
    · rintro ⟨earlier, owned⟩
      exact ⟨(ordered.ready_visible_iff cut ready actor
        (actor_output_visible (graph.nodes prior) who owned)).mpr earlier, owned⟩
    · rintro ⟨completed, owned⟩
      exact ⟨(ordered.ready_visible_iff cut ready actor
        (actor_output_visible (graph.nodes prior) who owned)).mp completed, owned⟩
  same_owner_ordered := by
    intro earlier later who before earlierActor laterActor
    exact ordered.visible_predecessor laterActor before
      (actor_output_visible (graph.nodes earlier) who earlierActor)

end Vegas.EventGraph
