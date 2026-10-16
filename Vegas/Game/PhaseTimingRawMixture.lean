/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPools

/-! # Exact raw perturbation tiers in operational timing mixtures -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- The raw-noise tier is the same actual uniform menu at every component,
including publicly excluded free choices and deliberate WAIT options. -/
theorem phaseTimingComponent_raw_mixture (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (part : PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)) :
    phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound wellFormed
        assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          agent part =
      mix noise noiseNonnegative noiseBounded
        ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1)
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed assessment 0 (by norm_num) (by norm_num) slotWeight slotNonnegative
            slotBounded agent part) := by
  classical
  let freeLaw := fun (agent : (N).InformationAgent (N).playedInformation)
    (choice : (N).Choice agent.1 agent.2.1) => PMF.pure choice
  let prescribed := fun agent : (N).InformationAgent (N).playedInformation =>
    mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler agent.1 agent.2.1)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler agent.1 agent.2.1)
  let timed := fun (agent : (N).InformationAgent (N).playedInformation) option =>
    mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler agent.1 agent.2.1)
      (phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler option agent.1 agent.2.1)
  let transform := fun (agent : (N).InformationAgent (N).playedInformation) law =>
    mix noise noiseNonnegative noiseBounded
      ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) law
  simpa only [phaseTimingComponent, phaseSourcePerturbedStrategy, phaseSourceTimingComponent,
    mix_zero, freeLaw, prescribed, timed, transform] using
      (freeKeyedComponent_transform freeLaw prescribed timed transform agent part)

private theorem bind_mix_fixed {Index Action : Type} (weights : PMF Index)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (raw : PMF Action) (conditional : Index → PMF Action) :
    weights.bind (fun part => mix noise nonnegative bounded raw (conditional part)) =
      mix noise nonnegative bounded raw (weights.bind conditional) := by
  calc
    _ = weights.bind (fun part => (mix noise nonnegative bounded (PMF.pure true)
        (PMF.pure false)).bind (fun selected => if selected then raw else conditional part)) := by
      apply congrArg (PMF.bind weights)
      funext part
      rw [mix_bind, PMF.pure_bind, PMF.pure_bind]
      rfl
    _ = (mix noise nonnegative bounded (PMF.pure true) (PMF.pure false)).bind
        (fun selected => weights.bind fun part => if selected then raw else conditional part) :=
      PMF.bind_comm ..
    _ = _ := by
      simp only [mix_bind, PMF.pure_bind, Bool.false_eq_true, ↓reduceIte, PMF.bind_const]

/-- Arbitrary actual pool weights retain exactly one common raw tier. The
remaining law uses those SAME weights with raw perturbation set to zero. -/
theorem phaseTimingComponent_mixture_raw_mixture (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (weights : PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent))) :
    weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        bound wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded agent) =
      mix noise noiseNonnegative noiseBounded
        ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1)
        (weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed assessment 0 (by norm_num) (by norm_num) slotWeight
            slotNonnegative slotBounded agent)) := by
  have component := phaseTimingComponent_raw_mixture setup mode runtime leaks bounds initial
    horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
      slotNonnegative slotBounded agent
  rw [funext component]
  exact bind_mix_fixed weights noise noiseNonnegative noiseBounded _ _

/-- Mapping an actual mixture atom splits its precise raw and residual
contributions. Accepted source failures stay in the residual contribution. -/
theorem phaseTimingComponent_mixture_raw_decomposition (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (weights : PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)))
    (response : Option (phaseApplication runtime leaks).Action) :
    (((weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        bound wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded agent)).map Subtype.val) response).toReal =
      noise * ((((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1).map
        Subtype.val) response).toReal +
      (1 - noise) * (((weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial
        horizon scheduler bound wellFormed assessment 0 (by norm_num) (by norm_num) slotWeight
          slotNonnegative slotBounded agent)).map Subtype.val) response).toReal := by
  rw [phaseTimingComponent_mixture_raw_mixture, mix_map, mix_apply_toReal]

end Vegas
