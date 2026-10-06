/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication

/-! # Service plans for event-addressed runtimes

A service plan is a list of instructions that reserve opportunities: a player
activation, a network opportunity, a reserved inclusion of an owner's latest
packet, a chance sample, a clock tick, or an expiry check. Only clock ticks
advance time. A sweep order visits every graph event once; it need not be
topological, since readiness is checked by the contract.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

variable {Player : Type}
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- One complete event sweep; its order need not be topological. Readiness is
checked by the contract, so visiting an unavailable event simply waits. -/
def ServiceOrder (graph : Vegas.EventGraph Player L) :=
  { events : List graph.EventId // events.Perm (List.finRange graph.order.eventCount) }

theorem ServiceOrder.mem (order : ServiceOrder graph) (event : graph.EventId) :
    event ∈ order.val :=
  order.property.mem_iff.mpr (List.mem_finRange event)

/-- A service instruction reserves an opportunity, never a player command. -/
inductive ServiceInstruction (graph : Vegas.EventGraph Player L) where
  | player (who : Player)
  | wire
  | includeLatest (event : graph.EventId) (owner : Player)
  | sample (event : graph.EventId)
  | tick
  | expire (event : graph.EventId)

/-- Only a clock instruction advances the clock. -/
def ServiceInstruction.ticks : ServiceInstruction graph → Nat
  | .tick => 1
  | _ => 0

def serviceTicks (plan : List (ServiceInstruction graph)) : Nat :=
  (plan.map ServiceInstruction.ticks).sum

@[simp] theorem serviceTicks_nil : serviceTicks ([] : List (ServiceInstruction graph)) = 0 :=
  rfl

@[simp] theorem serviceTicks_cons (instruction : ServiceInstruction graph)
    (rest : List (ServiceInstruction graph)) :
    serviceTicks (instruction :: rest) = instruction.ticks + serviceTicks rest := rfl

theorem serviceTicks_append (first second : List (ServiceInstruction graph)) :
    serviceTicks (first ++ second) = serviceTicks first + serviceTicks second := by
  simp [serviceTicks, List.sum_append]

/-- Every deadline is at least two clock ticks long, so an event enabled during
one sweep remains includable throughout the following clock-free sweep. -/
def ServiceFeasible (runtime : EventGraphRuntime graph) : Prop :=
  ∀ event, 2 ≤ runtime.deadline event

/-- Uniform upper bound on all local deadline lengths. -/
def maxDeadline (runtime : EventGraphRuntime graph) : Nat :=
  Finset.univ.sup runtime.deadline

/-- At most one full deadline window per graph event is needed for completion. -/
def serviceEpochs (runtime : EventGraphRuntime graph) : Nat :=
  graph.order.eventCount * (runtime.maxDeadline + 1)

end Vegas.EventGraphRuntime
