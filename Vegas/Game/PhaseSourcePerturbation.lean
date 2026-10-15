/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceSlotPolicy

/-! # Fully mixed native source recipes with independent slot and raw noise -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Independent weights leave the raw-noise rate available for the eventual
likelihood bounds. Every later unsent callback uses the same source recipe;
a silent response leaves later legal sending available. -/
def phaseSourcePerturbedStrategy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    ∀ who, (N).BehavioralPolicy who := fun who input =>
  mix noise noiseNonnegative noiseBounded
    ((menu).uniformPolicy initial horizon scheduler who input)
    (mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who input))

/-- Positive raw noise covers every actual finite-menu choice, without any
full-support hypothesis on the copied source assessment. -/
theorem phaseSourcePerturbedStrategy_fullSupport (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (positive : 0 < noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (input : (phaseApplication runtime leaks).Info) :
    FullSupport (phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise positive.le noiseBounded slotWeight slotNonnegative
        slotBounded who input) := by
  intro choice
  let := Fintype.ofFinite ((N).Choice who input)
  exact mem_support_mix_left _ _ _ positive (PMF.mem_support_uniformOfFintype choice)

/-- The canonical source response retains a uniform fraction of its original
mass. Both perturbation rates may be chosen after the source sequence. -/
theorem phaseSourcePerturbedStrategy_ge_main (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (input : (phaseApplication runtime leaks).Info)
    (choice : (N).Choice who input) :
    (1 - noise) * (1 - slotWeight) *
        ((phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial
          horizon scheduler who input) choice).toReal ≤
      ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded who input) choice).toReal := by
  unfold phaseSourcePerturbedStrategy
  rw [mix_apply_toReal, mix_apply_toReal]
  have uniform := ENNReal.toReal_nonneg (a :=
    ((menu).uniformPolicy initial horizon scheduler who input) choice)
  have slots := ENNReal.toReal_nonneg (a :=
    (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
      scheduler who input) choice)
  have first : 0 ≤ noise *
      (((menu).uniformPolicy initial horizon scheduler who input) choice).toReal :=
    mul_nonneg noiseNonnegative uniform
  have second : 0 ≤ (1 - noise) * (slotWeight *
      ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who input) choice).toReal) :=
    mul_nonneg (sub_nonneg.mpr noiseBounded) (mul_nonneg slotNonnegative slots)
  nlinarith

end Vegas
