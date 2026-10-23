/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseSeedOperationalInput

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
