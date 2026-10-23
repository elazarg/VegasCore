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
end Vegas.EventGraphRuntime.PhaseSeedCalendar
