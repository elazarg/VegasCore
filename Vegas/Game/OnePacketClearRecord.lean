/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForcedRegular

/-! # Clear public defaults imply the foreign public record -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- If no owner is publicly defaulted, every foreign owner remains active. -/
theorem publicRecord_of_clear {who : Player}
    {control : (application setup runtime leaks).Control}
    (clear : control.execution.application.config.defaulted = ∅) :
    PublicRecord setup runtime who control := by
  intro other _different excluded
  rw [clear] at excluded
  exact Finset.notMem_empty other excluded

end Vegas
