/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSlotTrembles

/-! # Slot retention

A slot-trembled component keeps the fraction
`(1 - scale³)(1 - scale²)(1 - scale)` of its main law (`Vegas.slotRetention`,
`Vegas.slotTrembledChoice_ge_main`), which tends to one along vanishing scales
(`Vegas.tendsto_slotRetention`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

/-- The fraction of its main law a slot-trembled component keeps. -/
def slotRetention (scale : ℝ) : ℝ := (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale)

theorem slotRetention_nonneg {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    0 ≤ slotRetention scale := by
  unfold slotRetention
  have : scale ^ 3 ≤ 1 := pow_le_one₀ nonnegative le_one
  have : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  have : 0 ≤ 1 - scale := by linarith
  have : 0 ≤ 1 - scale ^ 3 := by linarith
  have : 0 ≤ 1 - scale ^ 2 := by linarith
  positivity

theorem slotRetention_le_one {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    slotRetention scale ≤ 1 :=
  slotFactor_le_one nonnegative le_one

/-- Along vanishing tremble scales the slot retention tends to one. -/
theorem tendsto_slotRetention {scales : ℕ → ℝ} (vanishing : Tendsto scales atTop (nhds 0)) :
    Tendsto (fun n => slotRetention (scales n)) atTop (nhds 1) := by
  have limit := (((tendsto_const_nhds (x := (1 : ℝ))).sub (vanishing.pow 3)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (vanishing.pow 2))).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub vanishing)
  simpa [slotRetention] using limit

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

end Vegas
