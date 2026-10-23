/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryForeignExitBound

/-! # Native stopped payoff comparison with only foreign first-exclusion error

The comparison uses actual finite recovery policies and the induced native law.
Neither a global native service contract nor agreement after exclusion is needed.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime EventGraphRuntime.RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A classified first exit excluding other owners while this owner survives. -/
def ForeignExclusionLabel {History : Type} (who : Player) : Finset Player ⊕ History → Prop
  | .inl excluded => who ∉ excluded
  | .inr _ => False

end Vegas
