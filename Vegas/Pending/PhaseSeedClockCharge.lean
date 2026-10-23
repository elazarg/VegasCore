/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseSeedClosedBound
import Mathlib.Data.Fintype.Card
import Vegas.Pending.PhaseSeedScheduler

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

structure ClockCharge (runtime : EventGraphRuntime graph) where
  coordinate : PhaseSeedAddress graph
  tick : Nat
  entered : Nat
  entered_le : entered ≤ tick
  early : tick - entered < runtime.deadline coordinate.1.event
end Vegas.EventGraphRuntime.PhaseSeedCalendar
