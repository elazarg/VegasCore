/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Order
import Mathlib.Data.Finset.Lattice.Fold

/-! # Dependency depth and height in finite event orders -/

noncomputable section

namespace Vegas.EventOrder

/-- Number of dependency layers ending at an event. -/
def dependencyDepth (order : Vegas.EventOrder) (event : Fin order.eventCount) : Nat :=
  (order.predecessors event).attach.sup (fun predecessor =>
    dependencyDepth order predecessor.val) + 1
termination_by event.val
decreasing_by exact order.predecessor_lt predecessor.property

theorem predecessor_depth_lt (order : Vegas.EventOrder)
    {event predecessor : Fin order.eventCount}
    (member : predecessor ∈ order.predecessors event) :
    order.dependencyDepth predecessor < order.dependencyDepth event := by
  have lower := Finset.le_sup (f := fun point : {p // p ∈ order.predecessors event} =>
    order.dependencyDepth point.val) (Finset.mem_attach _ ⟨predecessor, member⟩)
  conv_rhs => rw [dependencyDepth]
  exact Nat.lt_succ_of_le lower

theorem dependencyDepth_pos (order : Vegas.EventOrder) (event : Fin order.eventCount) :
    0 < order.dependencyDepth event := by
  rw [dependencyDepth]
  omega

theorem dependencyDepth_le_index (order : Vegas.EventOrder) (event : Fin order.eventCount) :
    order.dependencyDepth event ≤ event.val + 1 := by
  have bound : ∀ index, ∀ event : Fin order.eventCount, event.val = index →
      order.dependencyDepth event ≤ index + 1 := by
    intro index
    induction index using Nat.strong_induction_on with
    | h index ih =>
        intro event same
        rw [dependencyDepth]
        have upper : (order.predecessors event).attach.sup
            (fun point => order.dependencyDepth point.val) ≤ index := by
          apply Finset.sup_le
          intro predecessor _
          have smaller := order.predecessor_lt predecessor.property
          have previous := ih predecessor.val.val (by omega) predecessor.val rfl
          omega
        omega
  exact bound event.val event rfl

/-- The longest dependency chain, with zero layers for the empty graph. -/
def dependencyHeight (order : Vegas.EventOrder) : Nat :=
  Finset.univ.sup order.dependencyDepth

theorem dependencyDepth_le_height (order : Vegas.EventOrder) (event : Fin order.eventCount) :
    order.dependencyDepth event ≤ order.dependencyHeight :=
  Finset.le_sup (f := order.dependencyDepth) (Finset.mem_univ event)

theorem dependencyHeight_le_eventCount (order : Vegas.EventOrder) :
    order.dependencyHeight ≤ order.eventCount := by
  apply Finset.sup_le
  intro event _
  have bound := order.dependencyDepth_le_index event
  have range := event.isLt
  omega

end Vegas.EventOrder
