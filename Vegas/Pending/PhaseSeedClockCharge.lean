/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedClosedBound
import Mathlib.Data.Fintype.Card

/-! # Finite physical-coordinate tickets for clock advancement

A clock advance is charged to an owned ready physical coordinate and its
relative tick, strictly before that event's deadline. The original activation
anchor makes a repeated ticket incompatible with strictly increasing clocks.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

abbrev ClockTicket (runtime : EventGraphRuntime graph) :=
  (coordinate : PhaseSeedAddress graph) × Fin (runtime.deadline coordinate.1.event)

structure ClockCharge (runtime : EventGraphRuntime graph) where
  coordinate : PhaseSeedAddress graph
  tick : Nat
  entered : Nat
  entered_le : entered ≤ tick
  early : tick - entered < runtime.deadline coordinate.1.event

namespace ClockCharge

def ticket {runtime : EventGraphRuntime graph} (charge : ClockCharge runtime) :
    ClockTicket runtime :=
  ⟨charge.coordinate, ⟨charge.tick - charge.entered, charge.early⟩⟩

omit [DecidableEq Player] in
/-- Original ready clocks, rather than raw global-time equality assumptions,
rule out reusing a clock ticket at a later genuine ready state. -/
theorem ticket_ne_of_ready_clock (runtime : EventGraphRuntime graph)
    (old fresh : ClockCharge runtime) (state : PhaseRuntimeState graph)
    (retained : ClosedCoordinateBound runtime old.tick old.entered old.coordinate.1 state)
    (current : fresh.tick = state.current.native.clock)
    (namespaceCurrent : fresh.coordinate.1.attempt = state.attempt)
    (ready : state.current.native.config.cut.Ready fresh.coordinate.1.event)
    (activated : state.current.native.activatedAt fresh.coordinate.1.event = some fresh.entered)
    (earlier : old.tick < state.current.native.clock) : old.ticket ≠ fresh.ticket := by
  intro same
  have coordinateEq : old.coordinate = fresh.coordinate := congrArg Sigma.fst same
  have elapsedEq : old.tick - old.entered = fresh.tick - fresh.entered :=
    congrArg (fun value : ClockTicket runtime => value.2.val) same
  have oldNamespace : old.coordinate.1.attempt = state.attempt := by
    rw [coordinateEq]
    exact namespaceCurrent
  rcases retained.event oldNamespace with completed | active
  · rw [coordinateEq] at completed
    exact ready.1 completed
  · have oldActivated := active.2.1
    rw [coordinateEq] at oldActivated
    have enteredEq : old.entered = fresh.entered :=
      Option.some.inj (oldActivated.symm.trans activated)
    have oldLe := old.entered_le
    have freshLe := fresh.entered_le
    omega

omit [DecidableEq Player] in
/-- The number of distinct advance tickets is bounded by the fixed original
all-attempt address space and the actual event deadlines. -/
theorem length_le_tickets (runtime : EventGraphRuntime graph)
    (charges : List (ClockCharge runtime)) (unique : (charges.map ticket).Nodup) :
    charges.length ≤ Fintype.card (ClockTicket runtime) := by
  simpa only [List.length_map] using unique.length_le_card

end ClockCharge
end Vegas.EventGraphRuntime.PhaseSeedCalendar
