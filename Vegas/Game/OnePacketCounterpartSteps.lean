module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketPairedCompletionMass
public import Vegas.Pending.EventValueSwap

@[expose] public section

/-! # Chance mass under a hidden swap

A hidden swap fixes every chance draw, so the chance mass of a completion is
that of its swap (`Vegas.completionMass_swap`).
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **A hidden swap fixes chance masses.** -/
theorem completionMass_swap (swap : HiddenSwap (graph setup))
    (before after : EventGraphRuntime.State (graph setup)) :
    completionMass setup (before.swap swap) (after.swap swap) =
      completionMass setup before after := by
  apply completionMass_eq_of_public
  · exact EventGraph.publicObserve_swap swap.values before.config
  · exact EventGraph.publicObserve_swap swap.values after.config

end Vegas
