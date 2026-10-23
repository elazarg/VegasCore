/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceObservation
import Vegas.Pending.RevealTranscript
import Vegas.Pending.EventSequentialTiming

/-! # Public calendar metadata at revelation checkpoints

Every source rank contributes its fixed number of ticks. The next event's
activation time is the preceding event's completion time: before those ticks
for a successful opening and after them for withholding. The public result
therefore determines the exact activation table, including with repeated owners.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Clock at the start of source rank `rank` in the existing service calendar. -/
def clockAt (rank : Nat) : Nat := (Finset.range rank).sum (fun prior => prior + 1)

theorem clockAt_succ (rank : Nat) : clockAt (rank + 1) = clockAt rank + (rank + 1) := by
  simp only [clockAt, Finset.sum_range_succ]

/-- The activation time is determined by the preceding public publication. -/
def checkpointEntryTime (accepted : AcceptedHandles (graph setup))
    (view : (graph setup).PublicObservation) : Nat :=
  match view.completionOrder.getLast? with
  | none => 0
  | some prior =>
      if (publicationPacket? accepted view.store prior).isSome
      then clockAt prior.val else clockAt (prior.val + 1)

/-- Sequential dependencies leave only the current rank active. At settlement
rank there is no event with that index, so the whole table is empty. -/
def checkpointActivations (accepted : AcceptedHandles (graph setup))
    (view : (graph setup).PublicObservation) (rank : Nat) :
    (graph setup).EventId → Option Nat := fun event =>
  if event.val = rank then some (checkpointEntryTime setup accepted view) else none

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
