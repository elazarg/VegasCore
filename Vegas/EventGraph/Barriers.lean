/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Information

/-! # Public-barrier event dependencies

Public events form barriers. Between them, different players' private bindings
can complete independently, while one player's own bindings retain their order.
The construction depends on typed outputs, not source values or player policies.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace EventField

/-- Two hidden binding events are controlled by the same player. -/
def SameBindingOwner : EventField Player L → EventField Player L → Prop
  | .binding left _, .binding right _ => left = right
  | _, _ => False

instance (left right : EventField Player L) : Decidable (left.SameBindingOwner right) := by
  cases left <;> cases right <;> simp only [SameBindingOwner] <;> infer_instance

end EventField

/-- Earlier public events, every event before a public barrier, and a player's
own earlier bindings are dependencies. Transitive dependencies through public
barriers follow from predecessor closure of cuts. -/
def barrierOrder {count : Nat} (outputs : Fin count → EventField Player L) : EventOrder where
  eventCount := count
  predecessors event := Finset.univ.filter fun prior =>
    prior.val < event.val ∧
      ((outputs prior).IsPublic ∨ (outputs event).IsPublic ∨
        (outputs prior).SameBindingOwner (outputs event))
  predecessor_lt := by
    intro event prior member
    exact (Finset.mem_filter.mp member).2.1

@[simp] theorem mem_barrierOrder {count : Nat}
    (outputs : Fin count → EventField Player L) (prior event : Fin count) :
    prior ∈ (barrierOrder outputs).predecessors event ↔
      prior.val < event.val ∧
        ((outputs prior).IsPublic ∨ (outputs event).IsPublic ∨
          (outputs prior).SameBindingOwner (outputs event)) := by
  simp [barrierOrder]

/-- A public event waits for every earlier event. -/
theorem barrierOrder_public_event {count : Nat}
    (outputs : Fin count → EventField Player L) {prior event : Fin count}
    (earlier : prior.val < event.val) (isPublic : (outputs event).IsPublic) :
    prior ∈ (barrierOrder outputs).predecessors event :=
  (mem_barrierOrder outputs prior event).mpr ⟨earlier, Or.inr (Or.inl isPublic)⟩

/-- Every event waits for all earlier public results. -/
theorem barrierOrder_public_prior {count : Nat}
    (outputs : Fin count → EventField Player L) {prior event : Fin count}
    (earlier : prior.val < event.val) (isPublic : (outputs prior).IsPublic) :
    prior ∈ (barrierOrder outputs).predecessors event :=
  (mem_barrierOrder outputs prior event).mpr ⟨earlier, Or.inl isPublic⟩

/-- One player's private action history retains its numeric source order. -/
theorem barrierOrder_same_owner {count : Nat}
    (outputs : Fin count → EventField Player L) {prior event : Fin count}
    (earlier : prior.val < event.val)
    (sameOwner : (outputs prior).SameBindingOwner (outputs event)) :
    prior ∈ (barrierOrder outputs).predecessors event :=
  (mem_barrierOrder outputs prior event).mpr ⟨earlier, Or.inr (Or.inr sameOwner)⟩

/-- A ready public event has exactly its source prefix completed. -/
theorem barrierOrder_ready_public_completed_iff {count : Nat}
    (outputs : Fin count → EventField Player L)
    (cut : (barrierOrder outputs).Cut) {event : Fin count}
    (ready : cut.Ready event) (isPublic : (outputs event).IsPublic)
    (other : Fin count) : other ∈ cut.completed ↔ other.val < event.val := by
  constructor
  · intro completed
    by_contra notEarlier
    have weak : event.val ≤ other.val := Nat.le_of_not_gt notEarlier
    rcases Nat.eq_or_lt_of_le weak with same | later
    · have eventEq : event = other := Fin.ext same
      exact ready.1 (eventEq ▸ completed)
    · exact ready.1 (cut.predecessor_closed completed
        (barrierOrder_public_prior outputs later isPublic))
  · intro earlier
    exact ready.2 (barrierOrder_public_event outputs earlier isPublic)

/-- At any ready event, the available public event fields are exactly the
earlier public fields. Later public results cannot overtake a strategic choice. -/
theorem barrierOrder_ready_public_field_iff {count : Nat}
    (outputs : Fin count → EventField Player L)
    (cut : (barrierOrder outputs).Cut) {event other : Fin count}
    (ready : cut.Ready event) (isPublic : (outputs other).IsPublic) :
    other ∈ cut.completed ↔ other.val < event.val := by
  constructor
  · intro completed
    by_contra notEarlier
    have weak : event.val ≤ other.val := Nat.le_of_not_gt notEarlier
    rcases Nat.eq_or_lt_of_le weak with same | later
    · have eventEq : event = other := Fin.ext same
      exact ready.1 (eventEq ▸ completed)
    · exact ready.1 (cut.predecessor_closed completed
        (barrierOrder_public_event outputs later isPublic))
  · intro earlier
    exact ready.2 (barrierOrder_public_prior outputs earlier isPublic)

end Vegas.EventGraph
