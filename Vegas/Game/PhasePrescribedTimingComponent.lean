/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingExclusionWeights

/-! # Timing components with fixed post-exclusion prescriptions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
    scheduler).InfoState who)]

local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

open Classical in
/-- Publicly excluded inputs have a fixed response law, independently of their
singleton pool part. All clear timing components retain the original family. -/
def phasePrescribedTimingComponent
    (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (prescribed : (agent : Agent) → PMF ((N).Choice agent.1 agent.2.1))
    (agent : Agent) (part : Parts (pool agent)) : PMF ((N).Choice agent.1 agent.2.1) :=
  if PhasePublicExclusion setup mode runtime leaks agent.2.1 then
    mix noise nonnegative bounded
      ((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon scheduler
        agent.1 agent.2.1) (prescribed agent)
  else phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
    wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded agent part

/-- Fixed post-exclusion prescriptions keep the original uniform RAW tier, so
every component still has full support on the entire counted native menu. -/
theorem phasePrescribedTimingComponent_fullSupport
    (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (positive : 0 < noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (prescribed : (agent : Agent) → PMF ((N).Choice agent.1 agent.2.1))
    (agent : Agent) (part : Parts (pool agent)) :
    FullSupport (phasePrescribedTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed source noise positive.le bounded slotWeight slotNonnegative
        slotBounded prescribed agent part) := by
  classical
  unfold phasePrescribedTimingComponent
  split
  · intro choice
    let := Fintype.ofFinite ((N).Choice agent.1 agent.2.1)
    exact mem_support_mix_left _ _ _ positive (PMF.mem_support_uniformOfFintype choice)
  · exact phaseTimingComponent_fullSupport setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed source noise positive bounded slotWeight slotNonnegative
        slotBounded agent part

/-- The constrained component family remains inside the original actual
timing mixtures, with only the free weights replaced by the fixed law. Thus
all arbitrary-weight clear timing and RAW estimates apply to this family. -/
theorem phasePrescribedTimingComponent_mixture
    (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (prescribed : (agent : Agent) → PMF ((N).Choice agent.1 agent.2.1))
    (agent : Agent) :
    (weights (pool agent)).bind
        (phasePrescribedTimingComponent setup mode runtime leaks bounds initial horizon scheduler
          bound wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded
            prescribed agent) =
      (phaseTimingWeightsWithExclusionLaw setup mode runtime leaks bounds initial horizon scheduler
        bound weights prescribed (pool agent)).bind
          (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded
              agent) := by
  classical
  by_cases excluded : PhasePublicExclusion setup mode runtime leaks agent.2.1
  · rw [phaseTimingComponent_with_exclusionLaw setup mode runtime leaks bounds initial horizon
      scheduler bound weights prescribed wellFormed source noise nonnegative bounded slotWeight
        slotNonnegative slotBounded agent excluded]
    calc
      _ = (weights (pool agent)).bind (fun _ => mix noise nonnegative bounded
          ((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon scheduler
            agent.1 agent.2.1) (prescribed agent)) := by
        apply congrArg ((weights (pool agent)).bind)
        funext part
        exact ite_eq_left excluded
      _ = _ := PMF.bind_const _ _
  · rw [phaseTimingWeightsWithExclusionLaw_of_clear setup mode runtime leaks bounds initial
      horizon scheduler bound weights prescribed agent excluded]
    apply congrArg ((weights (pool agent)).bind)
    funext part
    exact ite_eq_right excluded

end Vegas
