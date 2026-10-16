/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPools

/-! # Fresh operational timing keys along the complete owner recall -/

noncomputable section

namespace Vegas

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Equal timing keys retain the exact number of earlier owner responses. -/
theorem phaseTimingKey_recall_length (who : Player)
    (first second : List (phaseApplication runtime leaks).PlayerEntry)
    (firstView secondView : (phaseApplication runtime leaks).PlayerView)
    (same : phaseTimingKey runtime leaks who (some (first, firstView)) =
      phaseTimingKey runtime leaks who (some (second, secondView))) :
    first.length = second.length := by
  have lengths := congrArg (fun value => value.map (fun key => key.recalled.length)) same
  simpa only [phaseTimingKey, Option.map_some, List.length_map, Option.some.injEq] using lengths

/-- The key at a current input has not been queried at any recorded earlier
response, even if several earlier responses were identical silent actions. -/
theorem phaseTimingKey_fresh (who : Player)
    (past before : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (entry : (phaseApplication runtime leaks).PlayerEntry)
    (earlier : before ++ [entry] <+: past) :
    phaseTimingKey runtime leaks who (some (before, entry.beforeView)) ≠
      phaseTimingKey runtime leaks who (some (past, view)) := by
  intro same
  have lengths := phaseTimingKey_recall_length runtime leaks who before past entry.beforeView
    view same
  have shorter := earlier.length_le
  simp only [List.length_append, List.length_singleton] at shorter
  omega

end Vegas
