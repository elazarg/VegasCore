/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSlotTrembles
import GameTheoryExtensions.Math.Probability.TotalVariation

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

/-- Any response event disjoint from main support has total probability at most
square plus scale under the actual slot-trembled choice law. -/
theorem slotTrembledChoice_event_le_of_disjoint_main
    {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (event : Set ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (disjoint : Disjoint main.support event) :
    ((slotTrembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one
      who info main alternative slot).toOuterMeasure event).toReal ≤ scale ^ 2 + scale := by
  let retained := (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale)
  have close := PMF.WithinTV.of_domination main
    (slotTrembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one
      who info main alternative slot) retained (slotFactor_le_one nonnegative le_one)
    (fun choice => slotTrembledChoice_ge_main setup leaks bounds initial horizon scheduler
      nonnegative le_one who info main alternative slot choice)
  have zero : main.toOuterMeasure event = 0 :=
    (PMF.toOuterMeasure_apply_eq_zero_iff main event).mpr disjoint
  have comparison := close event
  rw [zero, ENNReal.toReal_zero, zero_sub, abs_neg,
    abs_of_nonneg ENNReal.toReal_nonneg] at comparison
  exact comparison.trans (by
    have lower := slotMainRetention_ge nonnegative le_one
    dsimp only [retained]
    linarith)

end Vegas
