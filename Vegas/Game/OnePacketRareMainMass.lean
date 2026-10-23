/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSlotTrembles

/-! # Probability of responses outside source-main support -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol Interaction EventGraphRuntime

/-- The retained main fraction loses at most the square plus the scale. -/
theorem slotMainRetention_ge {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    1 - (scale ^ 2 + scale) ≤ (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale) := by
  have inner : 0 ≤ 1 + scale * (1 - scale) :=
    add_nonneg zero_le_one (mul_nonneg nonnegative (sub_nonneg.mpr le_one))
  have remainder : 0 ≤ scale ^ 4 * (1 + scale * (1 - scale)) :=
    mul_nonneg (pow_nonneg nonnegative 4) inner
  have identity : (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale) -
      (1 - (scale ^ 2 + scale)) = scale ^ 4 * (1 + scale * (1 - scale)) := by ring
  linarith

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

end Vegas
