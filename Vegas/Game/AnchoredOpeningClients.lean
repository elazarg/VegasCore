/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AnchoredFirstTurnLaw

/-! # Reached boundaries

A *reached boundary* (`Vegas.ReachedBoundary`) is the execution of a legal
history at a scheduler boundary whose configuration is a prefix at some rank,
every later event still untouched, and every own submission made at its
author's turn.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- **A reached boundary.** The execution of a legal history at a scheduler
boundary, whose configuration is a prefix at `rank`, with every event from
`rank` on untouched and every own submission made at its author's turn. -/
structure ReachedBoundary (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (rank : Nat) (execution : (application setup leaks).Execution) : Prop where
  trace : Nonempty (((application setup leaks).protocol (initialLaw setup) horizon
    scheduler).Trace (some ⟨horizon - execution.environmentRecall.length, none, execution⟩))
  bounded : execution.environmentRecall.length ≤ horizon
  ordered : execution.application.config.cut.IsPrefix rank
  untouched : ∀ event : (graph setup).EventId, rank ≤ event.val →
    Untouched setup leaks event execution
  turns : ∀ who, OwnSubmissionsAtTurn setup leaks execution who

end Vegas
