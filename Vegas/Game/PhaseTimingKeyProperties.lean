/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPools

/-! # Public request data retained by operational timing keys -/

noncomputable section

namespace Vegas

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Equal complete operational timing keys retain literal current public
phase data, including request identities and inclusion deadlines. -/
theorem phaseTimingKey_publicView_eq (who : Player)
    (firstPast secondPast : List (app).PlayerEntry)
    (firstView secondView : (app).PlayerView)
    (same : phaseTimingKey runtime leaks who (some (firstPast, firstView)) =
      phaseTimingKey runtime leaks who (some (secondPast, secondView))) :
    firstView.application.2 = secondView.application.2 := by
  exact congrArg (fun key : PhaseTimingKey graph => key.current.application) (Option.some.inj same)

/-- Equal actual timing keys classify protected inclusion slack identically.
No posterior, probability or availability comparison is assumed. -/
theorem phaseUnprotected_iff_of_timingKey_eq (bound : graph.EventId → Nat) (who : Player)
    (firstPast secondPast : List (app).PlayerEntry)
    (firstView secondView : (app).PlayerView)
    (same : phaseTimingKey runtime leaks who (some (firstPast, firstView)) =
      phaseTimingKey runtime leaks who (some (secondPast, secondView))) :
    PhaseUnprotected runtime leaks bound who (some (firstPast, firstView)) ↔
      PhaseUnprotected runtime leaks bound who (some (secondPast, secondView)) := by
  have publicEq := phaseTimingKey_publicView_eq runtime leaks who firstPast secondPast
    firstView secondView same
  constructor
  · rintro ⟨past, view, event, equal, request, late⟩
    have equalView := congrArg Prod.snd (Option.some.inj equal)
    cases equalView
    refine ⟨secondPast, secondView, event, rfl, ?_, ?_⟩
    · rw [← publicEq]
      exact request
    · rw [← publicEq]
      exact late
  · rintro ⟨past, view, event, equal, request, late⟩
    have equalView := congrArg Prod.snd (Option.some.inj equal)
    cases equalView
    refine ⟨firstPast, firstView, event, rfl, ?_, ?_⟩
    · rw [publicEq]
      exact request
    · rw [publicEq]
      exact late

end Vegas
