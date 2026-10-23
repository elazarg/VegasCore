/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseSeedServiceMarks

/-! # Finite actual calendar rounds through every phase retry -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] [DecidableEq Player] in
theorem nonempty_of_namespace_progress (before after : PhaseRuntimeState graph)
    (progress : before.attempt.phase ≤ after.attempt.phase) (nonempty : after.phases ≠ []) :
    before.phases ≠ [] := by
  intro empty
  have prior : before.attempt.phase = graph.order.eventCount := by
    simp only [PhaseRuntimeState.attempt, empty, List.head?_nil, Option.map_none, Option.getD_none]
  cases phases : after.phases with
  | nil => exact nonempty phases
  | cons phase remaining =>
      have later : after.attempt.phase = phase.low := by
        simp only [PhaseRuntimeState.attempt, phases, List.head?_cons,
          Option.map_some, Option.getD_some]
      have lower := phase.nonempty
      have upper := phase.bounded
      omega

end Vegas.EventGraphRuntime.PhaseSeedCalendar
