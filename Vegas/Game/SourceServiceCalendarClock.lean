/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRuntime
import Vegas.EventGraph.CanonicalStep
import Vegas.Pending.EventSequentialTiming

/-! # Clock and ready rank of the source service calendar
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def clockAt (rank : Nat) : Nat := (Finset.range rank).sum (fun prior => prior + 1)

theorem clockAt_succ (rank : Nat) : clockAt (rank + 1) = clockAt rank + (rank + 1) := by
  simp only [clockAt, Finset.sum_range_succ]

theorem ready_iff_rank (config : (graph setup).Config) (rank : Nat)
    (ordered : config.cut.IsPrefix rank) (event : (graph setup).EventId) :
    config.cut.Ready event ↔ event.val = rank := by
  constructor
  · intro ready
    have lower : rank ≤ event.val := by
      by_contra earlier
      exact ready.1 ((ordered.2 event).mpr (by omega))
    have inside : rank < (graph setup).order.eventCount := by omega
    exact congrArg Fin.val (setup.eventGraph.sequentialize_ready_unique config.cut ready
      (ordered.ready inside))
  · intro same
    have inside : rank < (graph setup).order.eventCount := by omega
    have equal : event = ⟨rank, inside⟩ := Fin.ext same
    subst event
    exact ordered.ready inside

end Vegas
