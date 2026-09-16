/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.EventService

/-! # Event service regressions

The shared pending-message service schedules two independent binding events in
both orders.  These focused tests cover the concrete epoch plans, deadline
feasibility, and the event-addressed reserved selector.  Handler acceptance is
covered by the existing event-compilation runtime regressions.
-/

namespace VegasTests.EventService

open GameTheory.Math.Probability Interaction Vegas

noncomputable section

private abbrev pairOrder : EventOrder where
  eventCount := 2
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev pairInputs : Fin 0 → Vegas.EventGraph.EventField Bool simpleExpr := Fin.elim0

private abbrev pairOutputs : Fin 2 → Vegas.EventGraph.EventField Bool simpleExpr :=
  fun event => .binding (event.val == 1) .bool

private abbrev pairLayout := Vegas.EventGraph.fieldLayout pairInputs pairOutputs

private abbrev pairGraph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 0
  order := pairOrder
  inputLayout := pairInputs
  outputLayout := pairOutputs
  nodes event := Vegas.EventGraph.EventCode.bind (layout := pairLayout)
    (event.val == 1) .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private def runtime : EventGraphRuntime pairGraph where
  deadline _ := 2

private def firstPacket : Message Bool (EventGraphRuntime.Payload pairGraph) :=
  ⟨(false, 0), .commitment 0 (false, .prepared 0)⟩

private def unrelatedLater : Message Bool (EventGraphRuntime.Payload pairGraph) :=
  ⟨(false, 1), .commitment 1 (false, .prepared 1)⟩

private def firstPending : MessagePool Bool (EventGraphRuntime.Payload pairGraph) :=
  { MessagePool.empty Bool (EventGraphRuntime.Payload pairGraph) with
    pending := [firstPacket] }

/-- A newer packet by the same author but addressed to another event does not
consume the first event's reserved inclusion. -/
example :
    EventGraphRuntime.latestEventSubmission?
        { firstPending with pending := firstPending.pending ++ [unrelatedLater] }
        0 false =
      some firstPacket := by
  rw [EventGraphRuntime.latestEventSubmission?_append_nonmatching]
  · rfl
  · intro matching
    have addresses := matching.2
    change some (1 : Fin 2) = some 0 at addresses
    have same : (1 : Fin 2) = 0 := Option.some.inj addresses
    omega

/-- The shared epoch planner offers both independent bindings in increasing
order before the single clock tick and expiry pass. -/
example : EventGraphRuntime.epochPlan
    (EventGraphRuntime.ServiceOrder.increasing pairGraph) [] 0 =
    [.grant 0, .player false, .player false, .player false,
     .includeLatest 0 false, .sample 0,
     .grant 1, .player true, .player true, .player true,
     .includeLatest 1 true, .sample 1,
     .tick, .expire 0, .expire 1] := rfl

/-- The decreasing public service order offers the same events in the other
order without changing the expiry pass. -/
example : EventGraphRuntime.epochPlan
    (EventGraphRuntime.ServiceOrder.decreasing pairGraph) [] 0 =
    [.grant 1, .player true, .player true, .player true,
     .includeLatest 1 true, .sample 1,
     .grant 0, .player false, .player false, .player false,
     .includeLatest 0 false, .sample 0,
     .tick, .expire 0, .expire 1] := rfl

/-- The concrete deadline meets the service contract's one-following-epoch
grace requirement. -/
example : runtime.ServiceFeasible := by
  intro event
  rfl

end

end VegasTests.EventService
