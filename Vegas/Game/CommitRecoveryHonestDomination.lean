/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryHonestPrescription
import GameTheory.Analysis.Protocol.RestrictionDomination
import GameTheory.Analysis.Protocol.RestrictionBeliefs

/-! # Original honest likelihood retained by the actual normalized source law

All source perturbation scales are fixed before completion. The constructed
honest pins leave a common positive fraction of each original honest action,
independently of the completion weights and of any off-honest continuation.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))


end Vegas.SourceProgram.Setup
