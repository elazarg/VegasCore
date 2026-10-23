/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedClosedBound
import Vegas.Pending.PhaseSeedOperationalInput
import Vegas.Pending.PhaseSeedFreshness
import Vegas.Pending.PhaseSeedClockCharge
import Vegas.Pending.PhaseLive
import Vegas.Pending.PhaseSeedClockEffects
import Interaction.ReactiveTrafficState

/-! # Finite service receipts for actual all-event calendar rounds -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

inductive ServiceMark (graph : Vegas.EventGraph Player L) where
  | queried (activation : Bool) (tick : Nat) (coordinate : PhaseSeedAddress graph)
  | advanced (tick : Nat)
  | sampled (attempt : CommitAttemptId)

abbrev ServiceTicket (graph : Vegas.EventGraph Player L) :=
  (Bool × Nat × PhaseSeedAddress graph) ⊕ (Nat ⊕ CommitAttemptId)

namespace ServiceMark

def ticket : ServiceMark graph → ServiceTicket graph
  | .queried activation tick coordinate => .inl (activation, tick, coordinate)
  | .advanced tick => .inr (.inl tick)
  | .sampled attempt => .inr (.inr attempt)

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem retired_of_progress (attempt before after : CommitAttemptId)
    (generation : attempt.generation ≤ before.generation)
    (phase : attempt.phase ≤ before.phase) (different : attempt ≠ before)
    (progress : before.generation ≤ after.generation ∧ before.phase ≤ after.phase) :
    attempt ≠ after := by
  intro same
  apply different
  have phaseEq : attempt.phase = before.phase := by
    have := congrArg CommitAttemptId.phase same
    omega
  have generationEq : attempt.generation = before.generation := by
    have := congrArg CommitAttemptId.generation same
    omega
  cases attempt
  cases before
  exact congrArg₂ CommitAttemptId.mk phaseEq generationEq

open Classical in
/-- A fixed finite ticket reservoir covers clocks, both query replies per tick,
and every potential sample namespace. -/
def tickets : Finset (ServiceTicket graph) :=
  ((Finset.univ ×ˢ Finset.range (Fintype.card (ClockTicket runtime) + 1) ×ˢ Finset.univ).image
    Sum.inl) ∪
  ((Finset.range (Fintype.card (ClockTicket runtime))).image (Sum.inr ∘ Sum.inl)) ∪
  (((Finset.range (graph.order.eventCount + 1)) ×ˢ
    Finset.range (Fintype.card Player + 1)).image fun pair =>
      Sum.inr (Sum.inr (CommitAttemptId.mk pair.1 pair.2)))

end ServiceMark
end Vegas.EventGraphRuntime.PhaseSeedCalendar
