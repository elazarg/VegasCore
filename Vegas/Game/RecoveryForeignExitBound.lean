/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryExclusionPayoff
import GameTheory.Math.Probability.Bounds

/-! # Only foreign first exclusions contribute continuation error

At an own exclusion every whole continuation already pays the exclusion utility.
The stopped comparison assigns that utility to every exit; its discrepancy is
therefore confined to first exits that exclude only other owners.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A genuine recovery endpoint with at least one permanent public exclusion. -/
def RecoveryPublicExclusion :
    (recoveryApplication (runtime setup) leaks).ProtocolState → Prop
  | none => False
  | some control => control.execution.application.excluded ≠ ∅

end Vegas
