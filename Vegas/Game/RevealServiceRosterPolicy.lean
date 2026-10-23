/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService

/-! # One source policy over all visits of a revelation roster

These are policies on the existing native input: actual own recall and current
view. The source disclosure law and authentic opening are recovered from that
view. A fixed public roster supplies response-count offsets. Conditional timing
is a proof parameter for fully mixed approximants, not private runtime state.

The limiting policy explicitly stops after an opening. It does not evaluate a
zero-probability latent-mixture fallback at an off-path early opening. Coverage,
all-site consistency and sequential optimality remain separate obligations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def rosterOffset (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (event : (graph setup).EventId) : Nat :=
  (((List.finRange (graph setup).order.eventCount).take event.val).flatMap rosters).count who

/-- A timing law: for each event with an owner, a distribution over the owner's
visits in that event's roster. -/
abbrev TimingLaw (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) : Type :=
  ∀ event who, (graph setup).actor? event = some who → PMF (Fin ((rosters event).count who))

end Vegas
