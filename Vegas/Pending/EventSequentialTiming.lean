/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventInvariant
import Vegas.EventGraph.Sequential

/-! # Local deadlines between sequential events

Completing the current event makes its immediate successor ready and starts
that successor's clock at the actual completion time. Completing before the
block's ticks therefore ages the successor by exactly those ticks; completing
after them leaves its age zero. Increasing relative deadlines accommodate both
branches without assuming that the complete service calendar is timely.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.State

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A different sequential event cannot already have an activation time while
the current event is ready. This prevents inheriting an older deadline. -/
theorem Invariant.successor_not_activated {inputs : graph.sequentialize.Inputs}
    {state : State graph.sequentialize} (invariant : state.Invariant inputs)
    (event next : graph.sequentialize.EventId) (ready : state.config.cut.Ready event)
    (successor : next.val = event.val + 1) : state.activatedAt next = none := by
  cases activated : state.activatedAt next with
  | none => rfl
  | some entered =>
      have nextReady := (invariant.activated_iff next).mp
        (by simp only [activated, Option.isSome_some]) |>.1
      have same := graph.sequentialize_ready_unique state.config.cut ready nextReady
      have sameRank := congrArg Fin.val same
      omega

end Vegas.EventGraphRuntime.State
