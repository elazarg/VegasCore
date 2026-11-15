module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService

@[expose] public section

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
    (rosters : setup.informationGraph.EventId → List Player) (who : Player)
    (event : setup.informationGraph.EventId) : Nat :=
  (((List.finRange setup.informationGraph.order.eventCount).take event.val).flatMap rosters).count
    who

/-- A timing law: for each event with an owner, a distribution over the owner's
visits in that event's roster. -/
abbrev TimingLaw (setup : Setup (Player := Player) (L := L))
    (rosters : setup.informationGraph.EventId → List Player) : Type :=
  ∀ event who, setup.informationGraph.actor? event = some who → PMF (Fin ((rosters event).count
    who))

end Vegas
